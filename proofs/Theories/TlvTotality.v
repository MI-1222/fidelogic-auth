(** * TLVパーサーモデルの全域性(Totality)検証モジュール。 *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.

From Fidelogic Require Import Tactics.
From Fidelogic.Aeneas Require Import Primitives.
Import Primitives.
From Fidelogic.Theories Require Import FidelogicCore.
Import FidelogicCore.

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
