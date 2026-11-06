(** * TLVパーサーモデルの健全性検証モジュール。 *)

From Fidelogic.Aeneas Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.

From Fidelogic.Theories Require Import FidelogicCore.
Import FidelogicCore.

(** 補題 1: スライス長が2未満の場合、tlv_parse_tlv_header は必ず Ok None を返す。 *)
Lemma tlv_parse_tlv_header_underflow :
  forall (bytes : slice u8),
    (slice_len bytes s< 2%usize) = true ->
    tlv_parse_tlv_header bytes = Ok None.
Proof.
  intros bytes Hlen.
  unfold tlv_parse_tlv_header.
  rewrite Hlen.
  reflexivity.
Qed.

(** 補題 2: tlv_validate_tlv_bounds が true を返す場合、ヘッダーのパースは必ず成功（Some）している。 *)
Lemma tlv_validate_tlv_bounds_implies_header_some :
  forall (bytes : slice u8) (b : bool),
    tlv_validate_tlv_bounds bytes = Ok b ->
    b = true ->
    exists (hdr : tlv_TlvHeader_t),
      tlv_parse_tlv_header bytes = Ok (Some hdr).
Proof.
  intros bytes b Hval Htrue.
  unfold tlv_validate_tlv_bounds in Hval.
  destruct (tlv_parse_tlv_header bytes) as [opt_hdr | err] eqn:Hparse; [| discriminate].
  destruct opt_hdr as [hdr |].
  - exists hdr. reflexivity.
  - simpl in Hval. inversion Hval; subst. discriminate.
Qed.
