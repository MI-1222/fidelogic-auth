(** * DEKライフサイクル状態機械 (FSM) モジュール。 *)
(** [SPEC]
    本モジュールはマルチスロット型エンベロープ暗号化における、
    DEK (Data Encryption Key) のライフサイクル状態および基本決定論述語を形式定義する。 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.ZArith.
From Fidelogic Require Import Tactics.

Local Open Scope Z_scope.

(** [MODEL]
    平文DEK (Data Encryption Key) バイト列の型定義。
    256ビット (32バイト) の対称鍵を表す。 *)
Definition DekBytes : Type := list Z.

(** [MODEL]
    KEKスロット識別子の型定義。
    0: Argon2id (マスターパスワード), 1: WebAuthn PRF, 2: リカバリーコード。 *)
Definition SlotId : Type := nat.

(** [MODEL]
    DEKのライフサイクル状態を表す帰納型。
    Locked, Unlocking, Unlocked, Zeroized の4状態を定義する。 *)
Inductive VaultState : Type :=
  | Locked : VaultState
  | Unlocking : VaultState
  | Unlocked : VaultState
  | Zeroized : VaultState.

(** [SPEC]
    VaultState 間の決定可能等価性補題。 *)
Lemma vault_state_eq_dec : forall (s1 s2 : VaultState), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
Qed.

(** [MODEL]
    VaultState 間のブール値等価判定関数。 *)
Definition vault_state_eqb (s1 s2 : VaultState) : bool :=
  match s1, s2 with
  | Locked, Locked => true
  | Unlocking, Unlocking => true
  | Unlocked, Unlocked => true
  | Zeroized, Zeroized => true
  | _, _ => false
  end.

(** [SPEC]
    vault_state_eqb の反射性補題。 *)
Lemma vault_state_eqb_refl : forall (s : VaultState),
  vault_state_eqb s s = true.
Proof.
  destruct s; reflexivity.
Qed.

(** [SPEC]
    vault_state_eqb と等号命題の同値性補題。 *)
Lemma vault_state_eqb_eq : forall (s1 s2 : VaultState),
  vault_state_eqb s1 s2 = true <-> s1 = s2.
Proof.
  destruct s1; destruct s2; split; intro H;
    try reflexivity;
    try discriminate H.
Qed.

(** [SPEC]
    VaultState の有限網羅性補題。 *)
Lemma vault_state_cases : forall (s : VaultState),
  s = Locked \/ s = Unlocking \/ s = Unlocked \/ s = Zeroized.
Proof.
  destruct s; auto.
Qed.

(** [SPEC]
    Locked と Unlocked の状態排他性補題。 *)
Lemma vault_state_locked_not_unlocked : Locked <> Unlocked.
Proof.
  discriminate.
Qed.

(** [SPEC]
    Zeroized と Unlocked の状態排他性補題。 *)
Lemma vault_state_zeroized_not_unlocked : Zeroized <> Unlocked.
Proof.
  discriminate.
Qed.

(** [SPEC]
    Locked と Zeroized の状態排他性補題。 *)
Lemma vault_state_locked_not_zeroized : Locked <> Zeroized.
Proof.
  discriminate.
Qed.

(** [MODEL]
    暗号化Vaultマシンの実行時状態を表すレコード型。
    FSMコントロール状態 (VaultState) とメモリ内平文DEKバッファ (option DekBytes) を保持する。 *)
Record VaultMachineState : Type := mkVaultMachineState {
  vms_state : VaultState;
  vms_dek : option DekBytes;
}.

(** [MODEL]
    実行時状態から平文DEKを観測する射影関数。 *)
Definition observe_dek (m : VaultMachineState) : option DekBytes :=
  m.(vms_dek).

