(** * 今後の形式モデリング用プレースホルダーモジュール。 *)

From Stdlib Require Import Arith.PeanoNat.

(** [SPEC]
    恒等命題の健全性確認用補題。 *)
Lemma sanity_placeholder : forall (n : nat), n = n.
Proof.
  intros n.
  reflexivity.
Qed.
