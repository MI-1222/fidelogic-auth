(** * Fidelogic 形式検証基盤の疎通確認モジュール。 *)

From Stdlib Require Import Arith.PeanoNat.

(** [SPEC]
    加算の可換性に関する疎通確認用補題。 *)
Lemma sanity_add_comm : forall (n m : nat), n + m = m + n.
Proof.
  intros n m.
  apply Nat.add_comm.
Qed.
