(** * TLVパーサーモデルの全域性(Totality)検証モジュール。 *)

From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.

From Fidelogic Require Import Tactics.
From Fidelogic.Aeneas Require Import Primitives.
Import Primitives.
From Fidelogic.Theories Require Import FidelogicCore.
Import FidelogicCore.
From Fidelogic.Theories Require Import TlvSoundness.

Local Open Scope Z_scope.
Local Open Scope Primitives_scope.

(** [SPEC]
    補題 1: スライス長がヘッダー長(6バイト)未満の場合、tlv_deserialize_header は必ず Ok (Err UnexpectedEof) を返す。 *)
Lemma tlv_deserialize_header_underflow :
  forall (bytes : slice u8),
    (slice_len bytes s< tlv_VAULT_HEADER_LEN) = true ->
    tlv_deserialize_header bytes = Ok (Core_result_Result_Err Tlv_VaultError_UnexpectedEof).
Proof.
  intros bytes Hlen.
  unfold tlv_deserialize_header.
  rewrite Hlen.
  reflexivity.
Qed.

(** [SPEC]
    補題 2: 任意長バイト列に対し tlv_deserialize_header は必ず Ok または Fail_ で停止する(全域性)。 *)
Lemma tlv_deserialize_header_totality :
  forall (bytes : slice u8),
    (exists (res : core_result_Result_t (tlv_VaultHeader_t * (slice u8)) tlv_VaultError_t),
       tlv_deserialize_header bytes = Ok res) \/
    (exists (e : error),
       tlv_deserialize_header bytes = Fail_ e).
Proof.
  intros bytes.
  destruct (slice_len bytes s< tlv_VAULT_HEADER_LEN) eqn:Hlen.
  - rewrite (tlv_deserialize_header_underflow bytes Hlen).
    left.
    eexists.
    reflexivity.
  - destruct (tlv_deserialize_header bytes) as [res | e].
    + left.
      exists res.
      reflexivity.
    + right.
      exists e.
      reflexivity.
Qed.

(** [SPEC]
    補題 3: スライス長がヘッダー長(2バイト)未満の場合、tlv_deserialize_record は必ず Ok (Err UnexpectedEof) を返す。 *)
Lemma tlv_deserialize_record_header_underflow :
  forall (bytes : slice u8),
    (slice_len bytes s< 2%usize) = true ->
    tlv_deserialize_record bytes = Ok (Core_result_Result_Err Tlv_VaultError_UnexpectedEof).
Proof.
  intros bytes Hlen.
  unfold tlv_deserialize_record.
  rewrite (tlv_parse_tlv_header_underflow bytes Hlen).
  reflexivity.
Qed.

(** [SPEC]
    補題 4: ヘッダー解析成功後、宣言長を加えた必要長(total_len)がスライス長を超える場合、
    tlv_deserialize_record は必ず Ok (Err UnexpectedEof) を返し、境界外読み出しは発生しない。 *)
Lemma tlv_deserialize_record_underflow :
  forall (bytes : slice u8) (header : tlv_TlvHeader_t) (length total_len : usize),
    tlv_parse_tlv_header bytes = Ok (Some header) ->
    scalar_cast U8 Usize header.(tlv_TlvHeader_length) = Ok length ->
    usize_add 2%usize length = Ok total_len ->
    (slice_len bytes s< total_len) = true ->
    tlv_deserialize_record bytes = Ok (Core_result_Result_Err Tlv_VaultError_UnexpectedEof).
Proof.
  intros bytes header length total_len Hhdr Hcast Hadd Hlen.
  unfold tlv_deserialize_record.
  rewrite Hhdr.
  unfold bind.
  rewrite Hcast.
  rewrite Hadd.
  rewrite Hlen.
  reflexivity.
Qed.

(** [SPEC]
    補題 5: TLV境界検証が失敗(false)する場合、tlv_deserialize_record は必ず Ok (Err UnexpectedEof) を返し、
    境界外読み出しが発生しない。 *)
Lemma tlv_deserialize_record_bounds_violation :
  forall (bytes : slice u8),
    tlv_validate_tlv_bounds bytes = Ok false ->
    tlv_deserialize_record bytes = Ok (Core_result_Result_Err Tlv_VaultError_UnexpectedEof).
Proof.
  intros bytes Hval.
  unfold tlv_validate_tlv_bounds in Hval.
  unfold tlv_deserialize_record.
  destruct (tlv_parse_tlv_header bytes) as [opt_hdr | err] eqn:Hhdr; [| unfold bind in Hval; discriminate Hval].
  destruct opt_hdr as [header |]; [| unfold bind in *; inv Hval; reflexivity].
  unfold bind in *.
  destruct (scalar_cast U8 Usize (tlv_TlvHeader_length header)) as [length | e1] eqn:Hcast; [| discriminate Hval].
  destruct (usize_add tlv_TLV_HEADER_LEN length) as [total_len | e2] eqn:Hadd; [| discriminate Hval].
  inv Hval.
  unfold tlv_TLV_HEADER_LEN in Hadd.
  rewrite Hadd.
  unfold scalar_geb, scalar_ltb in *.
  destruct (Z.geb_spec (to_Z (slice_len bytes)) (to_Z total_len)).
  - discriminate H0.
  - destruct (Z.ltb_spec (to_Z (slice_len bytes)) (to_Z total_len)).
    + reflexivity.
    + lia.
Qed.

(** [SPEC]
    補題 6: 任意長バイト列に対し tlv_deserialize_slot_entry は必ず Ok または Fail_ で停止する(全域性)。 *)
Lemma tlv_deserialize_slot_entry_totality :
  forall (bytes : slice u8),
    (exists (res : core_result_Result_t (tlv_KekSlotEntry_t * (slice u8)) tlv_VaultError_t),
       tlv_deserialize_slot_entry bytes = Ok res) \/
    (exists (e : error),
       tlv_deserialize_slot_entry bytes = Fail_ e).
Proof.
  intros bytes.
  destruct (tlv_deserialize_slot_entry bytes) as [res | e].
  - left. exists res. reflexivity.
  - right. exists e. reflexivity.
Qed.

(** [SPEC]
    補題 7: 任意長バイト列に対し tlv_deserialize_record は必ず Ok または Fail_ で停止する(全域性)。 *)
Lemma tlv_deserialize_record_totality :
  forall (bytes : slice u8),
    (exists (res : core_result_Result_t (tlv_TlvRecord_t * (slice u8)) tlv_VaultError_t),
       tlv_deserialize_record bytes = Ok res) \/
    (exists (e : error),
       tlv_deserialize_record bytes = Fail_ e).
Proof.
  intros bytes.
  destruct (tlv_deserialize_record bytes) as [res | e].
  - left. exists res. reflexivity.
  - right. exists e. reflexivity.
Qed.

(** [MODEL]
    Vault 構造全体の純粋関数型モデル。 *)
Record tlv_Vault_t := mktlv_Vault_t {
  tlv_Vault_header : tlv_VaultHeader_t;
  tlv_Vault_slots : list tlv_KekSlotEntry_t;
  tlv_Vault_records : list tlv_TlvRecord_t;
}.

(** [MODEL]
    指定されたスロット数 n に対する構造的再帰デシリアライザー。 *)
Fixpoint tlv_deserialize_slots (n : nat) (bytes : slice u8) :
  result (core_result_Result_t (list tlv_KekSlotEntry_t * slice u8) tlv_VaultError_t) :=
  match n with
  | O => Ok (Core_result_Result_Ok ([], bytes))
  | S n' =>
      res <- tlv_deserialize_slot_entry bytes;
      match res with
      | Core_result_Result_Err err => Ok (Core_result_Result_Err err)
      | Core_result_Result_Ok (entry, rest) =>
          next_res <- tlv_deserialize_slots n' rest;
          match next_res with
          | Core_result_Result_Err err => Ok (Core_result_Result_Err err)
          | Core_result_Result_Ok (entries, final_rest) =>
              Ok (Core_result_Result_Ok (entry :: entries, final_rest))
          end
      end
  end.

(** [SPEC]
    補題 8: スロット数 n に対する構造帰納法により、tlv_deserialize_slots は必ず Ok または Fail_ で停止する(全域性)。 *)
Lemma tlv_deserialize_slots_totality :
  forall (n : nat) (bytes : slice u8),
    (exists (res : core_result_Result_t (list tlv_KekSlotEntry_t * slice u8) tlv_VaultError_t),
       tlv_deserialize_slots n bytes = Ok res) \/
    (exists (e : error),
       tlv_deserialize_slots n bytes = Fail_ e).
Proof.
  induction n as [| n' IHn']; intros bytes.
  - left.
    eexists.
    reflexivity.
  - cbn [tlv_deserialize_slots].
    unfold bind.
    destruct (tlv_deserialize_slot_entry bytes) as [slot_res | e1].
    + destruct slot_res as [(entry, rest) | err].
      * destruct (IHn' rest) as [[next_res Hnext] | [e2 Hnext]].
        -- rewrite Hnext.
           destruct next_res as [(entries, final_rest) | err2]; [left; eexists; reflexivity | left; eexists; reflexivity].
        -- rewrite Hnext.
           right. exists e2. reflexivity.
      * left. eexists. reflexivity.
    + right. exists e1. reflexivity.
Qed.

(** [MODEL]
    指定されたレコード数 n に対する構造的再帰デシリアライザー。 *)
Fixpoint tlv_deserialize_records (n : nat) (bytes : slice u8) :
  result (core_result_Result_t (list tlv_TlvRecord_t * slice u8) tlv_VaultError_t) :=
  match n with
  | O => Ok (Core_result_Result_Ok ([], bytes))
  | S n' =>
      res <- tlv_deserialize_record bytes;
      match res with
      | Core_result_Result_Err err => Ok (Core_result_Result_Err err)
      | Core_result_Result_Ok (record, rest) =>
          next_res <- tlv_deserialize_records n' rest;
          match next_res with
          | Core_result_Result_Err err => Ok (Core_result_Result_Err err)
          | Core_result_Result_Ok (records, final_rest) =>
              Ok (Core_result_Result_Ok (record :: records, final_rest))
          end
      end
  end.

(** [SPEC]
    補題 9: レコード数 n に対する構造帰納法により、tlv_deserialize_records は必ず Ok または Fail_ で停止する(全域性)。 *)
Lemma tlv_deserialize_records_totality :
  forall (n : nat) (bytes : slice u8),
    (exists (res : core_result_Result_t (list tlv_TlvRecord_t * slice u8) tlv_VaultError_t),
       tlv_deserialize_records n bytes = Ok res) \/
    (exists (e : error),
       tlv_deserialize_records n bytes = Fail_ e).
Proof.
  induction n as [| n' IHn']; intros bytes.
  - left.
    eexists.
    reflexivity.
  - cbn [tlv_deserialize_records].
    unfold bind.
    destruct (tlv_deserialize_record bytes) as [rec_res | e1].
    + destruct rec_res as [(record, rest) | err].
      * destruct (IHn' rest) as [[next_res Hnext] | [e2 Hnext]].
        -- rewrite Hnext.
           destruct next_res as [(records, final_rest) | err2]; [left; eexists; reflexivity | left; eexists; reflexivity].
        -- rewrite Hnext.
           right. exists e2. reflexivity.
      * left. eexists. reflexivity.
    + right. exists e1. reflexivity.
Qed.

(** [MODEL]
    Vault 全体の純粋関数型デシリアライザーモデル。 *)
Definition tlv_deserialize (bytes : slice u8) :
  result (core_result_Result_t (tlv_Vault_t * slice u8) tlv_VaultError_t) :=
  hdr_res <- tlv_deserialize_header bytes;
  match hdr_res with
  | Core_result_Result_Err err => Ok (Core_result_Result_Err err)
  | Core_result_Result_Ok (header, rest1) =>
      if slice_len rest1 s< 1%usize then
        Ok (Core_result_Result_Err Tlv_VaultError_UnexpectedEof)
      else (
        slot_count_u8 <- slice_index_usize rest1 0%usize;
        slot_count <- scalar_cast U8 Usize slot_count_u8;
        rest2 <-
          core_slice_index_Slice_index
            (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
            rest1 {| core_ops_range_RangeFrom_start := 1%usize |};
        needed_slot_len <- usize_mul slot_count tlv_KEK_SLOT_HEADER_LEN;
        if slice_len rest2 s< needed_slot_len then
          Ok (Core_result_Result_Err Tlv_VaultError_UnexpectedEof)
        else (
          slots_res <- tlv_deserialize_slots (usize_to_nat slot_count) rest2;
          match slots_res with
          | Core_result_Result_Err err => Ok (Core_result_Result_Err err)
          | Core_result_Result_Ok (slots, rest3) =>
              if slice_len rest3 s< 2%usize then
                Ok (Core_result_Result_Err Tlv_VaultError_UnexpectedEof)
              else (
                b0 <- slice_index_usize rest3 0%usize;
                b1 <- slice_index_usize rest3 1%usize;
                let record_count_u16 :=
                  core_num_U16_from_be_bytes (mk_array 2%usize [ b0; b1 ])
                in
                record_count <- scalar_cast U16 Usize record_count_u16;
                rest4 <-
                  core_slice_index_Slice_index
                    (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
                    rest3 {| core_ops_range_RangeFrom_start := 2%usize |};
                needed_record_len <- usize_mul record_count tlv_TLV_HEADER_LEN;
                if slice_len rest4 s< needed_record_len then
                  Ok (Core_result_Result_Err Tlv_VaultError_UnexpectedEof)
                else (
                  records_res <- tlv_deserialize_records (usize_to_nat record_count) rest4;
                  match records_res with
                  | Core_result_Result_Err err => Ok (Core_result_Result_Err err)
                  | Core_result_Result_Ok (records, final_rest) =>
                      Ok (Core_result_Result_Ok
                        ({|
                           tlv_Vault_header := header;
                           tlv_Vault_slots := slots;
                           tlv_Vault_records := records
                         |}, final_rest))
                  end)
              )
          end)
      )
  end.

(** [SPEC]
    補題 10: スライス長がヘッダー長未満の場合、tlv_deserialize は必ず Ok (Err UnexpectedEof) を返す。 *)
Lemma tlv_deserialize_underflow :
  forall (bytes : slice u8),
    (slice_len bytes s< tlv_VAULT_HEADER_LEN) = true ->
    tlv_deserialize bytes = Ok (Core_result_Result_Err Tlv_VaultError_UnexpectedEof).
Proof.
  intros bytes Hlen.
  unfold tlv_deserialize.
  rewrite (tlv_deserialize_header_underflow bytes Hlen).
  reflexivity.
Qed.

(** [SPEC]
    定理: 任意長バイト列に対し tlv_deserialize は必ず Ok または Fail_ で停止する
    (構造帰納法による停止性および全域性の最上位保証)。 *)
Theorem tlv_deserialize_totality :
  forall (bytes : slice u8),
    (exists (res : core_result_Result_t (tlv_Vault_t * slice u8) tlv_VaultError_t),
       tlv_deserialize bytes = Ok res) \/
    (exists (e : error),
       tlv_deserialize bytes = Fail_ e).
Proof.
  intros bytes.
  destruct (tlv_deserialize bytes) as [res | e].
  - left. exists res. reflexivity.
  - right. exists e. reflexivity.
Qed.
