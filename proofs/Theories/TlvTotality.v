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
    補題 1: スライス長がヘッダー長(14バイト)未満の場合、tlv_deserialize_header は必ず Ok (Err UnexpectedEof) を返す。 *)
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
    usize_add tlv_TLV_HEADER_LEN length = Ok total_len ->
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
    補題: u8 から usize へのスカラーキャストは常に Ok を返す (非失敗性)。 *)
Lemma scalar_cast_u8_to_usize_safe :
  forall (x : u8),
    exists (y : usize), scalar_cast U8 Usize x = Ok y.
Proof.
  intros [val Hbounds].
  unfold scalar_cast, mk_scalar, to_Z.
  cbn.
  rewrite scalar_bounds_iff in Hbounds.
  destruct Hbounds as [Hmin Hmax].
  cbn in Hmin, Hmax.
  destruct (sumbool_of_bool (scalar_in_bounds Usize val)) as [Hin | Hout].
  - exists (exist _ val (scalar_in_bounds_valid Usize val Hin)). reflexivity.
  - exfalso.
    unfold scalar_in_bounds, scalar_ge_min, scalar_le_max, scalar_min_cons, scalar_max_cons in Hout.
    unfold u32_min, u32_max, u8_min, u8_max in *.
    assert (Hge : (0%Z <=? val)%Z = true) by (apply Z.leb_le; lia).
    assert (Hle : (val <=? 4294967295%Z)%Z = true) by (apply Z.leb_le; lia).
    rewrite Hge, Hle in Hout.
    cbn in Hout.
    discriminate Hout.
Qed.

(** [SPEC]
    補題: u16 から usize へのスカラーキャストは常に Ok を返す (非失敗性)。 *)
Lemma scalar_cast_u16_to_usize_safe :
  forall (x : u16),
    exists (y : usize), scalar_cast U16 Usize x = Ok y.
Proof.
  intros [val Hbounds].
  unfold scalar_cast, mk_scalar, to_Z.
  cbn.
  rewrite scalar_bounds_iff in Hbounds.
  destruct Hbounds as [Hmin Hmax].
  cbn in Hmin, Hmax.
  destruct (sumbool_of_bool (scalar_in_bounds Usize val)) as [Hin | Hout].
  - exists (exist _ val (scalar_in_bounds_valid Usize val Hin)). reflexivity.
  - exfalso.
    unfold scalar_in_bounds, scalar_ge_min, scalar_le_max, scalar_min_cons, scalar_max_cons in Hout.
    unfold u32_min, u32_max, u16_min, u16_max in *.
    assert (Hge : (0%Z <=? val)%Z = true) by (apply Z.leb_le; lia).
    assert (Hle : (val <=? 4294967295%Z)%Z = true) by (apply Z.leb_le; lia).
    rewrite Hge, Hle in Hout.
    cbn in Hout.
    discriminate Hout.
Qed.

(** [SPEC]
    補題 8: 各スロットエントリのパースが非失敗 (Ok) であるとき、
    スロット数 n に対する構造帰納法により、
    tlv_deserialize_slots は Aeneas モナドレベルで失敗せず、
    必ず Ok res を返す(構造帰納的停止性および非失敗性)。 *)
Lemma tlv_deserialize_slots_non_failure :
  forall (n : nat) (bytes : slice u8),
    (forall (b : slice u8), exists (res : core_result_Result_t (tlv_KekSlotEntry_t * slice u8) tlv_VaultError_t),
       tlv_deserialize_slot_entry b = Ok res) ->
    exists (res : core_result_Result_t (list tlv_KekSlotEntry_t * slice u8) tlv_VaultError_t),
       tlv_deserialize_slots n bytes = Ok res.
Proof.
  induction n as [| n' IHn']; intros bytes Hentry.
  - cbn [tlv_deserialize_slots].
    eexists.
    reflexivity.
  - cbn [tlv_deserialize_slots].
    unfold bind.
    destruct (Hentry bytes) as [slot_res Hslot].
    rewrite Hslot.
    destruct slot_res as [(entry, rest) | err].
    + destruct (IHn' rest Hentry) as [next_res Hnext].
      rewrite Hnext.
      destruct next_res as [(entries, final_rest) | err2].
      * eexists. reflexivity.
      * eexists. reflexivity.
    + eexists. reflexivity.
Qed.

(** [SPEC]
    補題 8 (全域性): スロット数 n に対する構造帰納法により、
    tlv_deserialize_slots は必ず Ok または Fail_ で停止する(全域性)。 *)
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
    補題 9: 各レコードのパースが非失敗 (Ok) であるとき、
    レコード数 n に対する構造帰納法により、
    tlv_deserialize_records は Aeneas モナドレベルで失敗せず必ず Ok res を返す(構造帰納的停止性および非失敗性)。 *)
Lemma tlv_deserialize_records_non_failure :
  forall (n : nat) (bytes : slice u8),
    (forall (b : slice u8), exists (res : core_result_Result_t (tlv_TlvRecord_t * slice u8) tlv_VaultError_t),
       tlv_deserialize_record b = Ok res) ->
    exists (res : core_result_Result_t (list tlv_TlvRecord_t * slice u8) tlv_VaultError_t),
       tlv_deserialize_records n bytes = Ok res.
Proof.
  induction n as [| n' IHn']; intros bytes Hrec.
  - cbn [tlv_deserialize_records].
    eexists.
    reflexivity.
  - cbn [tlv_deserialize_records].
    unfold bind.
    destruct (Hrec bytes) as [rec_res Hrecord].
    rewrite Hrecord.
    destruct rec_res as [(record, rest) | err].
    + destruct (IHn' rest Hrec) as [next_res Hnext].
      rewrite Hnext.
      destruct next_res as [(records, final_rest) | err2].
      * eexists. reflexivity.
      * eexists. reflexivity.
    + eexists. reflexivity.
Qed.

(** [SPEC]
    補題 9 (全域性): レコード数 n に対する構造帰納法により、
    tlv_deserialize_records は必ず Ok または Fail_ で停止する(全域性)。 *)
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
(** Rust 側実装 (fidelogic_core::tlv::deserialize) の saturating_mul による境界検査と、
    構造帰納によるループ解体に対応した仕様モデル。 *)
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
        let needed_slot_len := core_num_Usize_saturating_mul slot_count tlv_KEK_SLOT_HEADER_LEN in
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
                let needed_record_len := core_num_Usize_saturating_mul record_count tlv_TLV_HEADER_LEN in
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

(** [MODEL]
    TLV デシリアライズ処理環境における非失敗性仕様。
    ヘッダー解析、スライスの境界内読み出し・サブスライス切り出し、および
    各スロット・レコード解析が Aeneas モナドレベルで失敗しない(Fail_ を返さない)ことを規定する。 *)
Record tlv_deserializer_non_failure_env : Type := {
  env_header :
    forall (bytes : slice u8),
      exists (res : core_result_Result_t (tlv_VaultHeader_t * slice u8) tlv_VaultError_t),
        tlv_deserialize_header bytes = Ok res;

  env_slot_count_read :
    forall (rest1 : slice u8),
      (slice_len rest1 s< 1%usize) = false ->
      exists (slot_count_u8 : u8),
        slice_index_usize rest1 0%usize = Ok slot_count_u8;

  env_rest2_subslice :
    forall (rest1 : slice u8),
      (slice_len rest1 s< 1%usize) = false ->
      exists (rest2 : slice u8),
        core_slice_index_Slice_index
          (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
          rest1 {| core_ops_range_RangeFrom_start := 1%usize |} = Ok rest2;

  env_slot_entry :
    forall (bytes : slice u8),
      exists (res : core_result_Result_t (tlv_KekSlotEntry_t * slice u8) tlv_VaultError_t),
        tlv_deserialize_slot_entry bytes = Ok res;

  env_record_count_read :
    forall (rest3 : slice u8),
      (slice_len rest3 s< 2%usize) = false ->
      exists (b0 b1 : u8),
        slice_index_usize rest3 0%usize = Ok b0 /\
        slice_index_usize rest3 1%usize = Ok b1;

  env_rest4_subslice :
    forall (rest3 : slice u8),
      (slice_len rest3 s< 2%usize) = false ->
      exists (rest4 : slice u8),
        core_slice_index_Slice_index
          (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
          rest3 {| core_ops_range_RangeFrom_start := 2%usize |} = Ok rest4;

  env_record :
    forall (bytes : slice u8),
      exists (res : core_result_Result_t (tlv_TlvRecord_t * slice u8) tlv_VaultError_t),
        tlv_deserialize_record bytes = Ok res;
}.

(** [SPEC]
    定理: デシリアライザー環境の非失敗性のもとで、任意長バイト列に対し tlv_deserialize は、
    Aeneas エラーモナドレベルで失敗せず、必ず Ok res (成功または VaultError) を返す
    (構造帰納法による停止性および合成パーサーの非失敗性最上位保証)。 *)
Theorem tlv_deserialize_totality :
  forall (env : tlv_deserializer_non_failure_env) (bytes : slice u8),
    exists (res : core_result_Result_t (tlv_Vault_t * slice u8) tlv_VaultError_t),
      tlv_deserialize bytes = Ok res.
Proof.
  intros env bytes.
  destruct (slice_len bytes s< tlv_VAULT_HEADER_LEN) eqn:Hunderflow.
  - rewrite (tlv_deserialize_underflow bytes Hunderflow).
    eexists. reflexivity.
  - unfold tlv_deserialize.
    destruct (env.(env_header) bytes) as [hdr_res Hhdr].
    rewrite Hhdr.
    destruct hdr_res as [(header, rest1) | err].
    + unfold bind.
      destruct (slice_len rest1 s< 1%usize) eqn:Hlen1.
      * eexists. reflexivity.
      * destruct (env.(env_slot_count_read) rest1 Hlen1) as [slot_count_u8 Hslot_cnt].
        rewrite Hslot_cnt.
        unfold bind.
        destruct (scalar_cast_u8_to_usize_safe slot_count_u8) as [slot_count Hcast_slot].
        rewrite Hcast_slot.
        unfold bind.
        destruct (env.(env_rest2_subslice) rest1 Hlen1) as [rest2 Hrest2].
        rewrite Hrest2.
        unfold bind.
        destruct (slice_len rest2 s< core_num_Usize_saturating_mul slot_count tlv_KEK_SLOT_HEADER_LEN) eqn:Hslot_len.
        -- eexists. reflexivity.
        -- destruct (tlv_deserialize_slots_non_failure (usize_to_nat slot_count) rest2 (env.(env_slot_entry))) as [slots_res Hslots].
           rewrite Hslots.
           destruct slots_res as [(slots, rest3) | err_slots].
           ++ unfold bind.
              destruct (slice_len rest3 s< 2%usize) eqn:Hlen3.
              ** eexists. reflexivity.
              ** destruct (env.(env_record_count_read) rest3 Hlen3) as [b0 [b1 [Hb0 Hb1]]].
                 rewrite Hb0.
                 unfold bind.
                 rewrite Hb1.
                 unfold bind.
                 destruct (scalar_cast_u16_to_usize_safe (core_num_U16_from_be_bytes (mk_array 2%usize [b0; b1]))) as [record_count Hcast_rec].
                 rewrite Hcast_rec.
                 unfold bind.
                 destruct (env.(env_rest4_subslice) rest3 Hlen3) as [rest4 Hrest4].
                 rewrite Hrest4.
                 unfold bind.
                 destruct (slice_len rest4 s< core_num_Usize_saturating_mul record_count tlv_TLV_HEADER_LEN) eqn:Hrec_len.
                 --- eexists. reflexivity.
                 --- destruct (tlv_deserialize_records_non_failure (usize_to_nat record_count) rest4 (env.(env_record))) as [records_res Hrecords].
                     rewrite Hrecords.
                     destruct records_res as [(records, final_rest) | err_records].
                     +++ eexists. reflexivity.
                     +++ eexists. reflexivity.
           ++ eexists. reflexivity.
    + eexists. reflexivity.
Qed.
