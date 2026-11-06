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
