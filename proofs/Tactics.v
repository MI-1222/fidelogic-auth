(** * Fidelogic プロジェクト共通 Ltac 証明タクティックおよび記法定義。 *)
(** [SPEC]
    本モジュールは `.agent/skills/rocq-ltac-*` スタイルガイドに準拠し、
    コンテキストの清浄性 (Context Cleanliness) や決定論的自動化階層を提供する。 *)

From Stdlib Require Import Lia.
From Stdlib Require Import List.

(** ** 破壊的等価置換タクティック (Context Cleanliness)
    仮定 [H] に対する inversion を行い、得られた等式を代入した上で不要となった仮定を消去する。 *)
Ltac inv H :=
  inversion H; subst; clear H.

(** 対象仮定を残しつつ代入のみを行うバリアント。 *)
Ltac invc H :=
  inversion H; subst.

(** ** 決定論的終端タクティック階層
    探索深さを安全域 (n <= 5) に制限した自動化タクティック。 *)
Ltac safe_auto :=
  auto.

Ltac safe_eauto :=
  eauto 3.
