(** * DEKライフサイクル状態機械 (FSM) モジュール。 *)
(** [SPEC]
    本モジュールはマルチスロット型エンベロープ暗号化における、
    DEK (Data Encryption Key) のライフサイクル状態および基本決定論述語を形式定義する。 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Arith.PeanoNat.
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

(** [MODEL]
    Slot 0: Argon2id (マスターパスワード) スロット識別子。 *)
Definition slot_argon2id : SlotId := 0%nat.

(** [MODEL]
    Slot 1: WebAuthn PRF スロット識別子。 *)
Definition slot_prf : SlotId := 1%nat.

(** [MODEL]
    Slot 2: リカバリーコード スロット識別子。 *)
Definition slot_recovery : SlotId := 2%nat.

(** [MODEL]
    有効なKEKスロット識別子 (0, 1, 2) を表すブール判定関数。 *)
Definition is_valid_slot_id (id : SlotId) : bool :=
  match id with
  | 0%nat => true
  | 1%nat => true
  | 2%nat => true
  | _ => false
  end.

(** [SPEC]
    有効なKEKスロット識別子 (0, 1, 2) を表す命題。 *)
Definition valid_slot_id (id : SlotId) : Prop :=
  id = slot_argon2id \/ id = slot_prf \/ id = slot_recovery.

(** [SPEC]
    is_valid_slot_id と valid_slot_id の同値性補題。 *)
Lemma valid_slot_id_eq : forall (id : SlotId),
  is_valid_slot_id id = true <-> valid_slot_id id.
Proof.
  intro id.
  unfold is_valid_slot_id, valid_slot_id, slot_argon2id, slot_prf, slot_recovery.
  destruct id as [|[|[|n]]].
  - split; intro H.
    + left. reflexivity.
    + reflexivity.
  - split; intro H.
    + right. left. reflexivity.
    + reflexivity.
  - split; intro H.
    + right. right. reflexivity.
    + reflexivity.
  - split; intro H.
    + discriminate H.
    + destruct H as [H | [H | H]]; inv H.
Qed.

(** [SPEC]
    Argon2id スロット識別子が有効であることを示す補題。 *)
Lemma valid_slot_id_argon2id : valid_slot_id slot_argon2id.
Proof.
  left. reflexivity.
Qed.

(** [SPEC]
    WebAuthn PRF スロット識別子が有効であることを示す補題。 *)
Lemma valid_slot_id_prf : valid_slot_id slot_prf.
Proof.
  right. left. reflexivity.
Qed.

(** [SPEC]
    リカバリーコード スロット識別子が有効であることを示す補題。 *)
Lemma valid_slot_id_recovery : valid_slot_id slot_recovery.
Proof.
  right. right. reflexivity.
Qed.

(** [MODEL]
    3つのKEKスロットの種別を表す帰納型。
    Argon2id, WebAuthn PRF, リカバリーコードの3種を定義する。 *)
Inductive SlotKind : Type :=
  | SlotArgon2id : SlotKind
  | SlotPrf : SlotKind
  | SlotRecovery : SlotKind.

(** [SPEC]
    SlotKind 間の決定可能等価性補題。 *)
Lemma slot_kind_eq_dec : forall (k1 k2 : SlotKind), {k1 = k2} + {k1 <> k2}.
Proof.
  decide equality.
Qed.

(** [MODEL]
    SlotKind から SlotId への射影関数。 *)
Definition slot_kind_to_id (k : SlotKind) : SlotId :=
  match k with
  | SlotArgon2id => slot_argon2id
  | SlotPrf => slot_prf
  | SlotRecovery => slot_recovery
  end.

(** [SPEC]
    slot_kind_to_id が生成するスロットIDは常に有効であることの健全性補題。 *)
Lemma slot_kind_to_id_valid : forall (k : SlotKind),
  valid_slot_id (slot_kind_to_id k).
Proof.
  destruct k; unfold valid_slot_id, slot_kind_to_id;
    try (left; reflexivity);
    try (right; left; reflexivity);
    try (right; right; reflexivity).
Qed.

(** [MODEL]
    KEKスロットの健全性状態を表す帰納型。
    SlotValid (復号可能・健全), SlotInvalid (データ破損・復号不能), SlotUnset (未設定・未登録) の3状態を定義する。 *)
Inductive SlotStatus : Type :=
  | SlotValid : SlotStatus
  | SlotInvalid : SlotStatus
  | SlotUnset : SlotStatus.

(** [SPEC]
    SlotStatus 間の決定可能等価性補題。 *)
Lemma slot_status_eq_dec : forall (s1 s2 : SlotStatus), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
Qed.

(** [MODEL]
    SlotStatus 間のブール値等価判定関数。 *)
Definition slot_status_eqb (s1 s2 : SlotStatus) : bool :=
  match s1, s2 with
  | SlotValid, SlotValid => true
  | SlotInvalid, SlotInvalid => true
  | SlotUnset, SlotUnset => true
  | _, _ => false
  end.

(** [SPEC]
    slot_status_eqb の反射性補題。 *)
Lemma slot_status_eqb_refl : forall (s : SlotStatus),
  slot_status_eqb s s = true.
Proof.
  destruct s; reflexivity.
Qed.

(** [SPEC]
    slot_status_eqb と等号命題の同値性補題。 *)
Lemma slot_status_eqb_eq : forall (s1 s2 : SlotStatus),
  slot_status_eqb s1 s2 = true <-> s1 = s2.
Proof.
  destruct s1; destruct s2; split; intro H;
    try reflexivity;
    try discriminate H.
Qed.

(** [SPEC]
    SlotStatus の有限網羅性補題。 *)
Lemma slot_status_cases : forall (s : SlotStatus),
  s = SlotValid \/ s = SlotInvalid \/ s = SlotUnset.
Proof.
  destruct s; auto.
Qed.

(** [SPEC]
    SlotValid と SlotInvalid の状態排他性補題。 *)
Lemma slot_status_valid_not_invalid : SlotValid <> SlotInvalid.
Proof.
  discriminate.
Qed.

(** [SPEC]
    SlotValid と SlotUnset の状態排他性補題。 *)
Lemma slot_status_valid_not_unset : SlotValid <> SlotUnset.
Proof.
  discriminate.
Qed.

(** [SPEC]
    SlotInvalid と SlotUnset の状態排他性補題。 *)
Lemma slot_status_invalid_not_unset : SlotInvalid <> SlotUnset.
Proof.
  discriminate.
Qed.

(** [MODEL]
    単一の SlotStatus が健全 (SlotValid) であるか判定するブール関数。 *)
Definition is_slot_status_valid (status : SlotStatus) : bool :=
  match status with
  | SlotValid => true
  | _ => false
  end.

(** [SPEC]
    is_slot_status_valid が true であることと SlotValid であることの同値性補題。 *)
Lemma is_slot_status_valid_eq : forall (s : SlotStatus),
  is_slot_status_valid s = true <-> s = SlotValid.
Proof.
  destruct s; split; intro H;
    try reflexivity;
    try discriminate H.
Qed.

(** [MODEL]
    3つのKEKスロット全体の健全性状態を保持するレコード型。
    Slot 0 (Argon2id), Slot 1 (WebAuthn PRF), Slot 2 (リカバリーコード) の状態を保持する。 *)
Record KekSlots : Type := mkKekSlots {
  slot_argon2id_status : SlotStatus;
  slot_prf_status : SlotStatus;
  slot_recovery_status : SlotStatus;
}.

(** [SPEC]
    KekSlots 間の決定可能等価性補題。 *)
Lemma kek_slots_eq_dec : forall (k1 k2 : KekSlots), {k1 = k2} + {k1 <> k2}.
Proof.
  decide equality.
  - apply slot_status_eq_dec.
  - apply slot_status_eq_dec.
  - apply slot_status_eq_dec.
Qed.

(** [MODEL]
    指定されたスロット識別子に対応する SlotStatus を取得する射影関数。
    IDが 0, 1, 2 以外の場合は SlotInvalid を返す。 *)
Definition get_slot_status (slots : KekSlots) (id : SlotId) : SlotStatus :=
  match id with
  | 0%nat => slots.(slot_argon2id_status)
  | 1%nat => slots.(slot_prf_status)
  | 2%nat => slots.(slot_recovery_status)
  | _ => SlotInvalid
  end.

(** [SPEC]
    get_slot_status の Slot 0 (Argon2id) に対する簡約補題。 *)
Lemma get_slot_status_argon2id : forall (slots : KekSlots),
  get_slot_status slots slot_argon2id = slots.(slot_argon2id_status).
Proof.
  intro slots. reflexivity.
Qed.

(** [SPEC]
    get_slot_status の Slot 1 (WebAuthn PRF) に対する簡約補題。 *)
Lemma get_slot_status_prf : forall (slots : KekSlots),
  get_slot_status slots slot_prf = slots.(slot_prf_status).
Proof.
  intro slots. reflexivity.
Qed.

(** [SPEC]
    get_slot_status の Slot 2 (リカバリーコード) に対する簡約補題。 *)
Lemma get_slot_status_recovery : forall (slots : KekSlots),
  get_slot_status slots slot_recovery = slots.(slot_recovery_status).
Proof.
  intro slots. reflexivity.
Qed.

(** [MODEL]
    指定されたスロット識別子のKEKスロットが健全 (復号可能) であるか判定するブール関数。 *)
Definition slot_validb (slots : KekSlots) (id : SlotId) : bool :=
  is_slot_status_valid (get_slot_status slots id).

(** [SPEC]
    指定されたスロット識別子のKEKスロットが健全 (ラップ済みDEKが復号可能) であることを表す述語。 *)
Definition slot_valid (slots : KekSlots) (id : SlotId) : Prop :=
  get_slot_status slots id = SlotValid.

(** [SPEC]
    slot_validb と slot_valid の同値性補題。 *)
Lemma slot_validb_eq : forall (slots : KekSlots) (id : SlotId),
  slot_validb slots id = true <-> slot_valid slots id.
Proof.
  intros slots id.
  unfold slot_validb, slot_valid.
  apply is_slot_status_valid_eq.
Qed.

(** [SPEC]
    境界外 (3以上) のスロット識別子は常に健全でないことを示す補題。 *)
Lemma slot_valid_out_of_bounds : forall (slots : KekSlots) (id : SlotId),
  (id <> slot_argon2id /\ id <> slot_prf /\ id <> slot_recovery) ->
  ~ slot_valid slots id.
Proof.
  intros slots id [H0 [H1 H2]].
  unfold slot_valid, get_slot_status.
  destruct id as [|[|[|n]]].
  - exfalso. apply H0. reflexivity.
  - exfalso. apply H1. reflexivity.
  - exfalso. apply H2. reflexivity.
  - intro H. discriminate H.
Qed.

(** [MODEL]
    3つのKEKスロットのうち少なくとも1つが健全であるか判定するブール関数。 *)
Definition any_slot_validb (slots : KekSlots) : bool :=
  slot_validb slots slot_argon2id ||
  slot_validb slots slot_prf ||
  slot_validb slots slot_recovery.

(** [SPEC]
    3つのKEKスロットのうち少なくとも1つが健全 (復号可能) であることを表す述語。 *)
Definition any_slot_valid (slots : KekSlots) : Prop :=
  slot_valid slots slot_argon2id \/
  slot_valid slots slot_prf \/
  slot_valid slots slot_recovery.

(** [SPEC]
    any_slot_validb と any_slot_valid の同値性補題。 *)
Lemma any_slot_validb_eq : forall (slots : KekSlots),
  any_slot_validb slots = true <-> any_slot_valid slots.
Proof.
  intros slots.
  unfold any_slot_validb, any_slot_valid.
  rewrite orb_true_iff.
  rewrite orb_true_iff.
  rewrite !slot_validb_eq.
  tauto.
Qed.

(** [SPEC]
    any_slot_valid と有効スロットに対する存在量化の同値性補題。 *)
Lemma any_slot_valid_exists_eq : forall (slots : KekSlots),
  any_slot_valid slots <-> (exists (id : SlotId), valid_slot_id id /\ slot_valid slots id).
Proof.
  intro slots.
  split.
  - intros [H0 | [H1 | H2]].
    + exists slot_argon2id. split.
      * left. reflexivity.
      * exact H0.
    + exists slot_prf. split.
      * right. left. reflexivity.
      * exact H1.
    + exists slot_recovery. split.
      * right. right. reflexivity.
      * exact H2.
  - intros [id [[H0 | [H1 | H2]] Hval]].
    + subst id. left. exact Hval.
    + subst id. right. left. exact Hval.
    + subst id. right. right. exact Hval.
Qed.

(** [SPEC]
    WebAuthn PRFスロットが無効または破損していても、Argon2idスロットが健全であれば全体の健全性が維持される補題。 *)
Lemma any_slot_valid_argon2id_robust : forall (slots : KekSlots),
  slot_valid slots slot_argon2id ->
  any_slot_valid slots.
Proof.
  intros slots H.
  left.
  exact H.
Qed.

(** [SPEC]
    WebAuthn PRFスロットが無効または破損していても、リカバリーコードスロットが健全であれば全体の健全性が維持される補題。 *)
Lemma any_slot_valid_recovery_robust : forall (slots : KekSlots),
  slot_valid slots slot_recovery ->
  any_slot_valid slots.
Proof.
  intros slots H.
  right. right.
  exact H.
Qed.

(** [MODEL]
    暗号化Vaultマシンの状態遷移を駆動するイベント (入力記号) を表す帰納型。 *)
Inductive VaultEvent : Type :=
  | EventStartUnlock : SlotId -> VaultEvent
  | EventUnlockSuccess : SlotId -> VaultEvent
  | EventUnlockFail : VaultEvent
  | EventLock : VaultEvent
  | EventZeroize : VaultEvent
  | EventReset : VaultEvent.

(** [SPEC]
    VaultEvent 間の決定可能等価性補題。 *)
Lemma vault_event_eq_dec : forall (e1 e2 : VaultEvent), {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply Nat.eq_dec.
Qed.

(** [SPEC]
    DEKライフサイクルにおける合法的かつ安全な状態遷移を規定する帰納的関係述語。
    スロット構成 (KekSlots) を環境パラメータとし、
    始点状態、入力イベント、終点状態の組が正当な遷移である条件を定義する。 *)
Inductive step (slots : KekSlots) : VaultState -> VaultEvent -> VaultState -> Prop :=
  | StepStartUnlock : forall (id : SlotId),
      valid_slot_id id ->
      step slots Locked (EventStartUnlock id) Unlocking
  | StepUnlockSuccess : forall (id : SlotId),
      slot_valid slots id ->
      step slots Unlocking (EventUnlockSuccess id) Unlocked
  | StepUnlockFail :
      step slots Unlocking EventUnlockFail Locked
  | StepLock :
      step slots Unlocked EventLock Locked
  | StepZeroize :
      step slots Unlocked EventZeroize Zeroized
  | StepReset :
      step slots Zeroized EventReset Locked.

(** [SPEC]
    状態遷移関係 step の決定論性補題。
    同一のスロット構成、始点状態、および入力イベントから遷移する終点状態は一意に定まる。 *)
Lemma step_deterministic : forall (slots : KekSlots) (s : VaultState) (ev : VaultEvent) (s1 s2 : VaultState),
  step slots s ev s1 ->
  step slots s ev s2 ->
  s1 = s2.
Proof.
  intros slots s ev s1 s2 H1 H2.
  inv H1; inv H2; reflexivity.
Qed.

(** [SPEC]
    Locked状態から任意の単一ステップ遷移によって直接Unlocked状態へ到達することは不可能であることを示す補題。 *)
Lemma step_locked_to_unlocked_impossible : forall (slots : KekSlots) (ev : VaultEvent),
  ~ step slots Locked ev Unlocked.
Proof.
  intros slots ev Hstep.
  inv Hstep.
Qed.

(** [SPEC]
    Zeroized状態から任意の単一ステップ遷移によって直接Unlocked状態へ到達することは不可能であることを示す補題。 *)
Lemma step_zeroized_to_unlocked_impossible : forall (slots : KekSlots) (ev : VaultEvent),
  ~ step slots Zeroized ev Unlocked.
Proof.
  intros slots ev Hstep.
  inv Hstep.
Qed.

(** [SPEC]
    EventUnlockSuccess による遷移が成立するためには、指定されたスロットが健全 (slot_valid) でなければならないことを示す補題。 *)
Lemma step_unlock_success_requires_valid : forall (slots : KekSlots) (id : SlotId) (s' : VaultState),
  step slots Unlocking (EventUnlockSuccess id) s' ->
  slot_valid slots id.
Proof.
  intros slots id s' Hstep.
  inv Hstep.
  assumption.
Qed.

(** [SPEC]
    EventStartUnlock による遷移が成立するためには、指定されたスロットIDが有効範囲内 (valid_slot_id) でなければならないことを示す補題。 *)
Lemma step_start_unlock_requires_valid_id : forall (slots : KekSlots) (id : SlotId) (s' : VaultState),
  step slots Locked (EventStartUnlock id) s' ->
  valid_slot_id id.
Proof.
  intros slots id s' Hstep.
  inv Hstep.
  assumption.
Qed.

(** [SPEC]
    Unlocked状態から退行する遷移は施錠 (EventLock) またはゼロ消去 (EventZeroize) のみであることを示す補題。 *)
Lemma step_unlocked_destinations : forall (slots : KekSlots) (ev : VaultEvent) (s' : VaultState),
  step slots Unlocked ev s' ->
  (ev = EventLock /\ s' = Locked) \/ (ev = EventZeroize /\ s' = Zeroized).
Proof.
  intros slots ev s' Hstep.
  inv Hstep.
  - left; split; reflexivity.
  - right; split; reflexivity.
Qed.

(** [SPEC]
    Locked状態からの遷移先は有効なスロットIDに対するEventStartUnlockによるUnlocking状態のみであることを示す補題。 *)
Lemma step_locked_destinations : forall (slots : KekSlots) (ev : VaultEvent) (s' : VaultState),
  step slots Locked ev s' ->
  exists (id : SlotId), ev = EventStartUnlock id /\ s' = Unlocking /\ valid_slot_id id.
Proof.
  intros slots ev s' Hstep.
  inv Hstep.
  exists id.
  split; [reflexivity | split; [reflexivity | assumption]].
Qed.

(** [SPEC]
    Zeroized状態からの遷移先はEventResetによるLocked状態のみであることを示す補題。 *)
Lemma step_zeroized_destinations : forall (slots : KekSlots) (ev : VaultEvent) (s' : VaultState),
  step slots Zeroized ev s' ->
  ev = EventReset /\ s' = Locked.
Proof.
  intros slots ev s' Hstep.
  inv Hstep.
  split; reflexivity.
Qed.

(** [SPEC]
    Unlocking状態からの遷移先は健全なスロットによるEventUnlockSuccess (Unlockedへ) またはEventUnlockFail (Lockedへ) のみであることを示す補題。 *)
Lemma step_unlocking_destinations : forall (slots : KekSlots) (ev : VaultEvent) (s' : VaultState),
  step slots Unlocking ev s' ->
  (exists (id : SlotId), ev = EventUnlockSuccess id /\ s' = Unlocked /\ slot_valid slots id) \/
  (ev = EventUnlockFail /\ s' = Locked).
Proof.
  intros slots ev s' Hstep.
  inv Hstep.
  - left. exists id. split; [reflexivity | split; [reflexivity | assumption]].
  - right. split; reflexivity.
Qed.

(** [MODEL]
    暗号化Vaultマシンの安全状態を表すブール判定関数。
    Locked, Unlocking, Zeroized 状態において平文DEKが None であることを検査する。
    Unlocked 状態では平文DEKの有無を問わず true を返す。 *)
Definition safe_stateb (m : VaultMachineState) : bool :=
  match m.(vms_state) with
  | Locked => match m.(vms_dek) with None => true | Some _ => false end
  | Unlocking => match m.(vms_dek) with None => true | Some _ => false end
  | Zeroized => match m.(vms_dek) with None => true | Some _ => false end
  | Unlocked => true
  end.

(** [SPEC]
    暗号化Vaultマシンの安全状態を表す述語。
    Locked, Unlocking, Zeroized 状態において平文DEKが None であることを構造的に保証する。
    Unlocked 状態では平文DEKの保持が許容される。 *)
Definition SafeState (m : VaultMachineState) : Prop :=
  match m.(vms_state) with
  | Locked => m.(vms_dek) = None
  | Unlocking => m.(vms_dek) = None
  | Zeroized => m.(vms_dek) = None
  | Unlocked => True
  end.

(** [SPEC]
    SafeState の別名表記 (スネークケース表記)。 *)
Notation safe_state := SafeState.

(** [SPEC]
    safe_stateb と SafeState の同値性補題。 *)
Lemma safe_stateb_eq : forall (m : VaultMachineState),
  safe_stateb m = true <-> SafeState m.
Proof.
  intro m.
  destruct m as [s dek].
  unfold safe_stateb, SafeState.
  destruct s; cbn.
  - destruct dek; split; intro H; try reflexivity; try discriminate H.
  - destruct dek; split; intro H; try reflexivity; try discriminate H.
  - split; intro H; [exact I | reflexivity].
  - destruct dek; split; intro H; try reflexivity; try discriminate H.
Qed.

(** [SPEC]
    SafeState の決定可能性補題。 *)
Lemma safe_state_dec : forall (m : VaultMachineState),
  {SafeState m} + {~ SafeState m}.
Proof.
  intro m.
  destruct (safe_stateb m) eqn:Eb.
  - left. apply safe_stateb_eq. exact Eb.
  - right. intro H.
    apply safe_stateb_eq in H.
    rewrite H in Eb.
    discriminate Eb.
Qed.

(** [SPEC]
    Locked状態において SafeState が成立しているならば平文DEKは None であることを示す補題。 *)
Lemma safe_state_locked : forall (m : VaultMachineState),
  m.(vms_state) = Locked ->
  SafeState m ->
  m.(vms_dek) = None.
Proof.
  intros [s dek] Hs Hsafe.
  cbn in Hs. subst s.
  exact Hsafe.
Qed.

(** [SPEC]
    Unlocking状態において SafeState が成立しているならば平文DEKは None であることを示す補題。 *)
Lemma safe_state_unlocking : forall (m : VaultMachineState),
  m.(vms_state) = Unlocking ->
  SafeState m ->
  m.(vms_dek) = None.
Proof.
  intros [s dek] Hs Hsafe.
  cbn in Hs. subst s.
  exact Hsafe.
Qed.

(** [SPEC]
    Zeroized状態において SafeState が成立しているならば平文DEKは None であることを示す補題。 *)
Lemma safe_state_zeroized : forall (m : VaultMachineState),
  m.(vms_state) = Zeroized ->
  SafeState m ->
  m.(vms_dek) = None.
Proof.
  intros [s dek] Hs Hsafe.
  cbn in Hs. subst s.
  exact Hsafe.
Qed.

(** [SPEC]
    Unlocked状態においては常に SafeState が成立することを示す補題。 *)
Lemma safe_state_unlocked : forall (m : VaultMachineState),
  m.(vms_state) = Unlocked ->
  SafeState m.
Proof.
  intros [s dek] Hs.
  cbn in Hs. subst s.
  exact I.
Qed.

(** [SPEC]
    Locked または Zeroized 状態において SafeState が成立しているならば平文DEKは None であることを示す補題。 *)
Lemma safe_state_locked_or_zeroized : forall (m : VaultMachineState),
  (m.(vms_state) = Locked \/ m.(vms_state) = Zeroized) ->
  SafeState m ->
  m.(vms_dek) = None.
Proof.
  intros m [Hl | Hz] Hsafe.
  - apply (safe_state_locked m Hl Hsafe).
  - apply (safe_state_zeroized m Hz Hsafe).
Qed.

(** [SPEC]
    Locked状態において SafeState が成立しているならば観測される平文DEKは None であることを示す補題。 *)
Lemma safe_state_observe_locked : forall (m : VaultMachineState),
  SafeState m ->
  m.(vms_state) = Locked ->
  observe_dek m = None.
Proof.
  intros m Hsafe Hs.
  unfold observe_dek.
  apply (safe_state_locked m Hs Hsafe).
Qed.

(** [SPEC]
    Unlocking状態において SafeState が成立しているならば観測される平文DEKは None であることを示す補題。 *)
Lemma safe_state_observe_unlocking : forall (m : VaultMachineState),
  SafeState m ->
  m.(vms_state) = Unlocking ->
  observe_dek m = None.
Proof.
  intros m Hsafe Hs.
  unfold observe_dek.
  apply (safe_state_unlocking m Hs Hsafe).
Qed.

(** [SPEC]
    Zeroized状態において SafeState が成立しているならば観測される平文DEKは None であることを示す補題。 *)
Lemma safe_state_observe_zeroized : forall (m : VaultMachineState),
  SafeState m ->
  m.(vms_state) = Zeroized ->
  observe_dek m = None.
Proof.
  intros m Hsafe Hs.
  unfold observe_dek.
  apply (safe_state_zeroized m Hs Hsafe).
Qed.

(** [SPEC]
    Locked または Zeroized 状態において SafeState が成立しているならば観測される平文DEKは None であることを示す補題。 *)
Lemma safe_state_observe_locked_or_zeroized : forall (m : VaultMachineState),
  SafeState m ->
  (m.(vms_state) = Locked \/ m.(vms_state) = Zeroized) ->
  observe_dek m = None.
Proof.
  intros m Hsafe [Hl | Hz].
  - apply (safe_state_observe_locked m Hsafe Hl).
  - apply (safe_state_observe_zeroized m Hsafe Hz).
Qed.

(** [SPEC]
    SafeState を満たすマシン状態において平文DEKが観測される場合、状態は必ず Unlocked であることを示す補題。 *)
Lemma safe_state_observe_some_implies_unlocked : forall (m : VaultMachineState) (k : DekBytes),
  SafeState m ->
  observe_dek m = Some k ->
  m.(vms_state) = Unlocked.
Proof.
  intros [s dek] k Hsafe Hobs.
  unfold observe_dek in Hobs. cbn in Hobs.
  destruct s.
  - assert (Hnone := safe_state_locked {| vms_state := Locked; vms_dek := dek |} eq_refl Hsafe).
    cbn in Hnone. rewrite Hnone in Hobs. discriminate Hobs.
  - assert (Hnone := safe_state_unlocking {| vms_state := Unlocking; vms_dek := dek |} eq_refl Hsafe).
    cbn in Hnone. rewrite Hnone in Hobs. discriminate Hobs.
  - reflexivity.
  - assert (Hnone := safe_state_zeroized {| vms_state := Zeroized; vms_dek := dek |} eq_refl Hsafe).
    cbn in Hnone. rewrite Hnone in Hobs. discriminate Hobs.
Qed.

(** [SPEC]
    メモリ内平文DEKバッファが None であるならば、いかなる状態であっても常に SafeState を満たすことを示す補題。 *)
Lemma safe_state_intro_none : forall (m : VaultMachineState),
  m.(vms_dek) = None ->
  SafeState m.
Proof.
  intros [s dek] Hdek.
  cbn in Hdek.
  destruct s; cbn; try exact Hdek; try exact I.
Qed.

(** [SPEC]
    初期マシン状態 (Locked かつ平文DEK None) は常に SafeState を満たすことを示す補題。 *)
Lemma safe_state_init :
  SafeState (mkVaultMachineState Locked None).
Proof.
  apply safe_state_intro_none.
  reflexivity.
Qed.

(** [SPEC]
    DEKライフサイクルにおける多段階状態遷移を表す帰納的関係述語。
    入力イベント列 (トレース) を先頭から順次消費しながら状態を更新する。 *)
Inductive steps (slots : KekSlots) : VaultState -> list VaultEvent -> VaultState -> Prop :=
  | StepsNil : forall (s : VaultState),
      steps slots s [] s
  | StepsCons : forall (s1 s2 s3 : VaultState) (ev : VaultEvent) (trace : list VaultEvent),
      step slots s1 ev s2 ->
      steps slots s2 trace s3 ->
      steps slots s1 (ev :: trace) s3.

(** [SPEC]
    多段階状態遷移 steps の反射性補題。
    空のイベント列において状態は変化しない。 *)
Lemma steps_refl : forall (slots : KekSlots) (s : VaultState),
  steps slots s [] s.
Proof.
  intros slots s.
  apply StepsNil.
Qed.

(** [SPEC]
    単一ステップ遷移 step を長さ1のイベント列による多段階遷移 steps へ持ち上げる補題。 *)
Lemma steps_step : forall (slots : KekSlots) (s1 : VaultState) (ev : VaultEvent) (s2 : VaultState),
  step slots s1 ev s2 ->
  steps slots s1 [ev] s2.
Proof.
  intros slots s1 ev s2 Hstep.
  apply (StepsCons slots s1 s2 s2 ev [] Hstep (StepsNil slots s2)).
Qed.

(** [SPEC]
    多段階状態遷移 steps の推移性 (トレース連結) 補題。
    2つのイベント列を連結した実行列が多段階遷移を満たすことを示す。 *)
Lemma steps_trans : forall (slots : KekSlots) (s1 s2 s3 : VaultState) (tr1 tr2 : list VaultEvent),
  steps slots s1 tr1 s2 ->
  steps slots s2 tr2 s3 ->
  steps slots s1 (tr1 ++ tr2) s3.
Proof.
  intros slots s1 s2 s3 tr1 tr2 H1 H2.
  induction H1 as [s | s_a s_b s_c ev tr Hstep Hsteps IH].
  - cbn. exact H2.
  - cbn.
    apply (StepsCons slots s_a s_b s3 ev (tr ++ tr2) Hstep (IH H2)).
Qed.

(** [SPEC]
    VaultMachineState (実行時マシン状態) に対する単一ステップ遷移関係述語。
    FSMコントロール状態遷移に伴い、メモリ内平文DEKバッファ (vms_dek) の安全なロードおよび消去を規定する。 *)
Inductive machine_step (slots : KekSlots) : VaultMachineState -> VaultEvent -> VaultMachineState -> Prop :=
  | MStepStartUnlock : forall (id : SlotId),
      valid_slot_id id ->
      machine_step slots
        (mkVaultMachineState Locked None)
        (EventStartUnlock id)
        (mkVaultMachineState Unlocking None)
  | MStepUnlockSuccess : forall (id : SlotId) (k : DekBytes),
      slot_valid slots id ->
      machine_step slots
        (mkVaultMachineState Unlocking None)
        (EventUnlockSuccess id)
        (mkVaultMachineState Unlocked (Some k))
  | MStepUnlockFail :
      machine_step slots
        (mkVaultMachineState Unlocking None)
        EventUnlockFail
        (mkVaultMachineState Locked None)
  | MStepLock : forall (dek : option DekBytes),
      machine_step slots
        (mkVaultMachineState Unlocked dek)
        EventLock
        (mkVaultMachineState Locked None)
  | MStepZeroize : forall (dek : option DekBytes),
      machine_step slots
        (mkVaultMachineState Unlocked dek)
        EventZeroize
        (mkVaultMachineState Zeroized None)
  | MStepReset :
      machine_step slots
        (mkVaultMachineState Zeroized None)
        EventReset
        (mkVaultMachineState Locked None).

(** [SPEC]
    VaultMachineState に対する多段階状態遷移関係述語。 *)
Inductive machine_steps (slots : KekSlots) : VaultMachineState -> list VaultEvent -> VaultMachineState -> Prop :=
  | MStepsNil : forall (m : VaultMachineState),
      machine_steps slots m [] m
  | MStepsCons : forall (m1 m2 m3 : VaultMachineState) (ev : VaultEvent) (trace : list VaultEvent),
      machine_step slots m1 ev m2 ->
      machine_steps slots m2 trace m3 ->
      machine_steps slots m1 (ev :: trace) m3.

(** [SPEC]
    machine_step からコントロール状態の step への射影補題。 *)
Lemma machine_step_to_step : forall (slots : KekSlots) (m1 : VaultMachineState) (ev : VaultEvent) (m2 : VaultMachineState),
  machine_step slots m1 ev m2 ->
  step slots m1.(vms_state) ev m2.(vms_state).
Proof.
  intros slots m1 ev m2 Hstep.
  inv Hstep; cbn; constructor; assumption.
Qed.

(** [SPEC]
    machine_steps からコントロール状態の steps への射影補題。 *)
Lemma machine_steps_to_steps : forall (slots : KekSlots) (m1 : VaultMachineState) (trace : list VaultEvent) (m2 : VaultMachineState),
  machine_steps slots m1 trace m2 ->
  steps slots m1.(vms_state) trace m2.(vms_state).
Proof.
  intros slots m1 trace m2 Hsteps.
  induction Hsteps as [m | m1' m2' m3' ev tr Hstep Hsteps' IH].
  - constructor.
  - econstructor.
    + apply (machine_step_to_step slots m1' ev m2' Hstep).
    + exact IH.
Qed.

(** [SPEC]
    machine_step に対する安全状態不変条件の保存性補題 (Invariant Preservation)。
    始点マシン状態が SafeState を満たすならば、任意の単一ステップ遷移後の終点マシン状態も SafeState を満たす。 *)
Lemma machine_step_preserves_safe_state : forall (slots : KekSlots) (m1 : VaultMachineState) (ev : VaultEvent) (m2 : VaultMachineState),
  SafeState m1 ->
  machine_step slots m1 ev m2 ->
  SafeState m2.
Proof.
  intros slots m1 ev m2 Hsafe Hstep.
  inv Hstep; cbn; try reflexivity; try exact I.
Qed.

(** [SPEC]
    machine_steps に対する安全状態不変条件の保存性定理 (Multi-step Invariant Preservation)。
    始点マシン状態が SafeState を満たすならば、任意の遷移列を経た終点マシン状態も常に SafeState を満たす。 *)
Theorem machine_steps_preserves_safe_state : forall (slots : KekSlots) (m1 : VaultMachineState) (trace : list VaultEvent) (m2 : VaultMachineState),
  SafeState m1 ->
  machine_steps slots m1 trace m2 ->
  SafeState m2.
Proof.
  intros slots m1 trace m2 Hsafe Hsteps.
  induction Hsteps as [m | m1' m2' m3' ev tr Hstep Hsteps' IH].
  - exact Hsafe.
  - apply IH.
    apply (machine_step_preserves_safe_state slots m1' ev m2' Hsafe Hstep).
Qed.

(** [MODEL]
    ある初期状態から目標状態へ到達可能であることを表す到達可能性述語。 *)
Definition can_reach (slots : KekSlots) (from to : VaultState) : Prop :=
  exists (trace : list VaultEvent), steps slots from trace to.

(** [SPEC]
    指定されたスロットIDが有効範囲内かつ健全であるならば、
    EventStartUnlock と EventUnlockSuccess からなる2ステップトレースによって
    Locked状態からUnlocked状態へ到達可能であることを示す補題。 *)
Lemma slot_unlock_trace : forall (slots : KekSlots) (id : SlotId),
  valid_slot_id id ->
  slot_valid slots id ->
  steps slots Locked [EventStartUnlock id; EventUnlockSuccess id] Unlocked.
Proof.
  intros slots id Hvalid Hslot.
  apply (StepsCons slots Locked Unlocking Unlocked (EventStartUnlock id) [EventUnlockSuccess id]).
  - apply StepStartUnlock. exact Hvalid.
  - apply (StepsCons slots Unlocking Unlocked Unlocked (EventUnlockSuccess id) []).
    + apply StepUnlockSuccess. exact Hslot.
    + apply StepsNil.
Qed.

(** [SPEC]
    Argon2idスロットが健全であるならば、Locked状態からUnlocked状態へ2ステップで到達可能であることを示す補題。 *)
Lemma slot_unlock_argon2id : forall (slots : KekSlots),
  slot_valid slots slot_argon2id ->
  steps slots Locked [EventStartUnlock slot_argon2id; EventUnlockSuccess slot_argon2id] Unlocked.
Proof.
  intros slots Hslot.
  apply slot_unlock_trace.
  - apply valid_slot_id_argon2id.
  - exact Hslot.
Qed.

(** [SPEC]
    WebAuthn PRFスロットが健全であるならば、Locked状態からUnlocked状態へ2ステップで到達可能であることを示す補題。 *)
Lemma slot_unlock_prf : forall (slots : KekSlots),
  slot_valid slots slot_prf ->
  steps slots Locked [EventStartUnlock slot_prf; EventUnlockSuccess slot_prf] Unlocked.
Proof.
  intros slots Hslot.
  apply slot_unlock_trace.
  - apply valid_slot_id_prf.
  - exact Hslot.
Qed.

(** [SPEC]
    リカバリーコードスロットが健全であるならば、Locked状態からUnlocked状態へ2ステップで到達可能であることを示す補題。 *)
Lemma slot_unlock_recovery : forall (slots : KekSlots),
  slot_valid slots slot_recovery ->
  steps slots Locked [EventStartUnlock slot_recovery; EventUnlockSuccess slot_recovery] Unlocked.
Proof.
  intros slots Hslot.
  apply slot_unlock_trace.
  - apply valid_slot_id_recovery.
  - exact Hslot.
Qed.

(** [SPEC]
    スロット多重化健全性定理 (Slot Multiplexing Completeness Theorem)。
    3つのKEKスロット (Argon2id, WebAuthn PRF, リカバリーコード) のうちいずれか1つが健全 (slot_valid) であれば、
    実行時マシンは合法的状態遷移列 (steps) により Locked 状態から Unlocked 状態へ到達可能であることを保証する。 *)
Theorem slot_multiplexing_soundness : forall (slots : KekSlots),
  any_slot_valid slots ->
  exists (trace : list VaultEvent), steps slots Locked trace Unlocked.
Proof.
  intros slots Hany.
  apply any_slot_valid_exists_eq in Hany.
  destruct Hany as [id [Hvalid Hslot]].
  exists [EventStartUnlock id; EventUnlockSuccess id].
  apply (slot_unlock_trace slots id Hvalid Hslot).
Qed.

(** [SPEC]
    到達可能性述語 can_reach を用いたスロット多重化健全性定理の系。
    いずれかのスロットが健全であれば can_reach により Locked から Unlocked への到達可能性が成立する。 *)
Corollary slot_multiplexing_can_reach : forall (slots : KekSlots),
  any_slot_valid slots ->
  can_reach slots Locked Unlocked.
Proof.
  intros slots Hany.
  unfold can_reach.
  apply (slot_multiplexing_soundness slots Hany).
Qed.

(** [MODEL]
    指定されたイベントが有効な認証イベント (健全なスロットに対する解錠成功イベント) であるかを判定するブール関数。 *)
Definition is_valid_unlock_eventb (slots : KekSlots) (ev : VaultEvent) : bool :=
  match ev with
  | EventUnlockSuccess id => slot_validb slots id
  | _ => false
  end.

(** [SPEC]
    指定されたイベントが有効な認証イベント (健全なスロットに対する解錠成功イベント) であることを表す述語。 *)
Definition valid_unlock_event (slots : KekSlots) (ev : VaultEvent) : Prop :=
  exists (id : SlotId), ev = EventUnlockSuccess id /\ slot_valid slots id.

(** [SPEC]
    is_valid_unlock_eventb と valid_unlock_event の同値性補題。 *)
Lemma is_valid_unlock_eventb_eq : forall (slots : KekSlots) (ev : VaultEvent),
  is_valid_unlock_eventb slots ev = true <-> valid_unlock_event slots ev.
Proof.
  intros slots ev.
  unfold is_valid_unlock_eventb, valid_unlock_event.
  destruct ev as [id | id | | | | ].
  - split; intro H.
    + discriminate H.
    + destruct H as [id0 [Heq Hval]]. discriminate Heq.
  - split; intro H.
    + exists id. split; [reflexivity |].
      apply slot_validb_eq. exact H.
    + destruct H as [id0 [Heq Hval]].
      inv Heq.
      apply slot_validb_eq. exact Hval.
  - split; intro H; [discriminate H | destruct H as [id0 [Heq _]]; discriminate Heq].
  - split; intro H; [discriminate H | destruct H as [id0 [Heq _]]; discriminate Heq].
  - split; intro H; [discriminate H | destruct H as [id0 [Heq _]]; discriminate Heq].
  - split; intro H; [discriminate H | destruct H as [id0 [Heq _]]; discriminate Heq].
Qed.

(** [MODEL]
    指定されたイベントが構文的に解錠成功イベント (EventUnlockSuccess) であるかを判定するブール関数。 *)
Definition is_unlock_success_eventb (ev : VaultEvent) : bool :=
  match ev with
  | EventUnlockSuccess _ => true
  | _ => false
  end.

(** [SPEC]
    指定されたイベントが構文的に解錠成功イベント (EventUnlockSuccess) であることを表す述語。 *)
Definition unlock_success_event (ev : VaultEvent) : Prop :=
  exists (id : SlotId), ev = EventUnlockSuccess id.

(** [SPEC]
    is_unlock_success_eventb と unlock_success_event の同値性補題。 *)
Lemma is_unlock_success_eventb_eq : forall (ev : VaultEvent),
  is_unlock_success_eventb ev = true <-> unlock_success_event ev.
Proof.
  intro ev.
  unfold is_unlock_success_eventb, unlock_success_event.
  destruct ev as [id | id | | | | ].
  - split; intro H; [discriminate H | destruct H as [id0 Heq]; discriminate Heq].
  - split; intro H; [exists id; reflexivity | reflexivity].
  - split; intro H; [discriminate H | destruct H as [id0 Heq]; discriminate Heq].
  - split; intro H; [discriminate H | destruct H as [id0 Heq]; discriminate Heq].
  - split; intro H; [discriminate H | destruct H as [id0 Heq]; discriminate Heq].
  - split; intro H; [discriminate H | destruct H as [id0 Heq]; discriminate Heq].
Qed.

(** [SPEC]
    構文的解錠成功イベントでないならば、いかなるスロット構成に対しても有効な認証イベントになり得ないことを示す補題。 *)
Lemma not_unlock_success_implies_not_valid_unlock : forall (slots : KekSlots) (ev : VaultEvent),
  ~ unlock_success_event ev ->
  ~ valid_unlock_event slots ev.
Proof.
  intros slots ev Hnot [id [Heq Hval]].
  apply Hnot.
  exists id. exact Heq.
Qed.

(** [SPEC]
    イベント列に有効な認証イベントが含まれないこと (未認証トレース) を表す述語。 *)
Definition no_valid_unlock_trace (slots : KekSlots) (trace : list VaultEvent) : Prop :=
  Forall (fun ev => ~ valid_unlock_event slots ev) trace.

(** [MODEL]
    イベント列に有効な認証イベントが含まれないかを判定するブール関数。 *)
Definition no_valid_unlock_traceb (slots : KekSlots) (trace : list VaultEvent) : bool :=
  forallb (fun ev => negb (is_valid_unlock_eventb slots ev)) trace.

(** [SPEC]
    no_valid_unlock_traceb と no_valid_unlock_trace の同値性補題。 *)
Lemma no_valid_unlock_traceb_eq : forall (slots : KekSlots) (trace : list VaultEvent),
  no_valid_unlock_traceb slots trace = true <-> no_valid_unlock_trace slots trace.
Proof.
  intros slots trace.
  unfold no_valid_unlock_traceb, no_valid_unlock_trace.
  rewrite forallb_forall.
  rewrite Forall_forall.
  split; intros H ev Hin.
  - specialize (H ev Hin).
    apply negb_true_iff in H.
    intro Hval.
    apply is_valid_unlock_eventb_eq in Hval.
    rewrite Hval in H.
    discriminate H.
  - specialize (H ev Hin).
    apply negb_true_iff.
    destruct (is_valid_unlock_eventb slots ev) eqn:Eb.
    + apply is_valid_unlock_eventb_eq in Eb.
      exfalso. apply (H Eb).
    + reflexivity.
Qed.

(** [SPEC]
    イベント列に構文的な解錠成功イベントが一切含まれないことを表す述語。 *)
Definition no_unlock_success_trace (trace : list VaultEvent) : Prop :=
  Forall (fun ev => ~ unlock_success_event ev) trace.

(** [SPEC]
    構文的に解錠成功イベントを含まないトレースは、任意の環境において未認証トレースとなることを示す補題。 *)
Lemma no_unlock_success_implies_no_valid_unlock_trace : forall (slots : KekSlots) (trace : list VaultEvent),
  no_unlock_success_trace trace ->
  no_valid_unlock_trace slots trace.
Proof.
  intros slots trace Htrace.
  unfold no_unlock_success_trace in Htrace.
  unfold no_valid_unlock_trace.
  rewrite Forall_forall in *.
  intros ev Hin.
  specialize (Htrace ev Hin).
  apply not_unlock_success_implies_not_valid_unlock.
  exact Htrace.
Qed.

(** [SPEC]
    非解錠状態集合 (Locked, Unlocking, Zeroized) から有効な認証イベントを経ない単一ステップ遷移において、
    遷移先の状態も必ず非解錠状態 (Locked, Unlocking, Zeroized) にとどまることを示す1ステップ保存補題。 *)
Lemma step_non_unlocked_invariant : forall (slots : KekSlots) (s1 : VaultState) (ev : VaultEvent) (s2 : VaultState),
  s1 <> Unlocked ->
  ~ valid_unlock_event slots ev ->
  step slots s1 ev s2 ->
  s2 <> Unlocked.
Proof.
  intros slots s1 ev s2 Hs1 Hnot_auth Hstep.
  assert (Hcases : s1 = Locked \/ s1 = Unlocking \/ s1 = Zeroized).
  {
    destruct s1.
    - left. reflexivity.
    - right. left. reflexivity.
    - exfalso. apply Hs1. reflexivity.
    - right. right. reflexivity.
  }
  destruct Hcases as [HL | [HU | HZ]].
  - subst s1.
    apply step_locked_destinations in Hstep.
    destruct Hstep as [id [Hev [Hs2 Hval]]].
    subst s2. discriminate.
  - subst s1.
    apply step_unlocking_destinations in Hstep.
    destruct Hstep as [[id [Hev [Hs2 Hval]]] | [Hev Hs2]].
    + exfalso. apply Hnot_auth.
      exists id. split; [exact Hev | exact Hval].
    + subst s2. discriminate.
  - subst s1.
    apply step_zeroized_destinations in Hstep.
    destruct Hstep as [Hev Hs2].
    subst s2. discriminate.
Qed.

(** [SPEC]
    非解錠状態 (s1 <> Unlocked) から有効な認証イベントを含まない多段階遷移列 (steps) により
    到達可能な任意の状態 s2 は、決して Unlocked にはなり得ないことを示す一般化トレース不変性定理。 *)
Theorem steps_non_unlocked_invariant : forall (slots : KekSlots) (s1 : VaultState) (trace : list VaultEvent) (s2 : VaultState),
  s1 <> Unlocked ->
  no_valid_unlock_trace slots trace ->
  steps slots s1 trace s2 ->
  s2 <> Unlocked.
Proof.
  intros slots s1 trace s2 Hs1 Htrace Hsteps.
  generalize dependent Hs1.
  induction Hsteps as [s | s_a s_b s_c ev tr Hstep Hsteps' IH].
  - intros Hs_curr. exact Hs_curr.
  - intros Hs_a.
    inv Htrace.
    assert (Hs_b : s_b <> Unlocked).
    {
      apply (step_non_unlocked_invariant slots s_a ev s_b Hs_a H1 Hstep).
    }
    apply (IH H2 Hs_b).
Qed.

(** [SPEC]
    非到達性定理 (FSM Reachability Soundness Theorem)。
    施錠状態 (Locked) から出発し、有効な認証イベントを経由しない任意の遷移列 (steps) によって、
    解錠状態 (Unlocked) に到達することは不可能であることを保証する。 *)
Theorem locked_no_auth_unreachability : forall (slots : KekSlots) (trace : list VaultEvent) (s : VaultState),
  no_valid_unlock_trace slots trace ->
  steps slots Locked trace s ->
  s <> Unlocked.
Proof.
  intros slots trace s Htrace Hsteps.
  apply (steps_non_unlocked_invariant slots Locked trace s vault_state_locked_not_unlocked Htrace Hsteps).
Qed.

(** [SPEC]
    構文的に解錠成功イベントを一切含まないトレースに対する非到達性定理の系。 *)
Corollary locked_syntax_no_auth_unreachability : forall (slots : KekSlots) (trace : list VaultEvent) (s : VaultState),
  no_unlock_success_trace trace ->
  steps slots Locked trace s ->
  s <> Unlocked.
Proof.
  intros slots trace s Htrace Hsteps.
  apply (locked_no_auth_unreachability slots trace s).
  - apply (no_unlock_success_implies_no_valid_unlock_trace slots trace Htrace).
  - exact Hsteps.
Qed.

(** [SPEC]
    非解錠状態起点における一般化DEK平文非露出定理 (Generalized Non-Unlocked Data Plane Confidentiality Theorem)。
    非解錠状態 (vms_state m_init <> Unlocked) かつ安全なマシン状態 (SafeState m_init) から出発して
    有効な認証イベントを経ずに遷移した任意のマシン状態 m においては、
    平文DEKが観測されることはなく、常に None が保たれることを保証する。 *)
Theorem non_unlocked_no_auth_dek_confidentiality : forall (slots : KekSlots) (trace : list VaultEvent) (m_init m : VaultMachineState),
  SafeState m_init ->
  m_init.(vms_state) <> Unlocked ->
  machine_steps slots m_init trace m ->
  no_valid_unlock_trace slots trace ->
  observe_dek m = None.
Proof.
  intros slots trace m_init m Hsafe_init Hnot_unlocked_init Hsteps Htrace.
  assert (Hsteps_ctrl : steps slots m_init.(vms_state) trace m.(vms_state)).
  {
    apply (machine_steps_to_steps slots m_init trace m Hsteps).
  }
  assert (Hnot_unlocked : m.(vms_state) <> Unlocked).
  {
    apply (steps_non_unlocked_invariant slots m_init.(vms_state) trace m.(vms_state) Hnot_unlocked_init Htrace Hsteps_ctrl).
  }
  assert (Hsafe : SafeState m).
  {
    apply (machine_steps_preserves_safe_state slots m_init trace m Hsafe_init Hsteps).
  }
  destruct (observe_dek m) as [k | ] eqn:Eobs.
  - assert (Hunlocked := safe_state_observe_some_implies_unlocked m k Hsafe Eobs).
    exfalso. apply (Hnot_unlocked Hunlocked).
  - reflexivity.
Qed.

(** [SPEC]
    非解錠状態起点における一般化DEK平文非抽出系 (Generalized Non-Unlocked Cannot Extract DEK Corollary)。 *)
Corollary non_unlocked_no_auth_cannot_extract_dek : forall (slots : KekSlots) (trace : list VaultEvent) (m_init m : VaultMachineState) (k : DekBytes),
  SafeState m_init ->
  m_init.(vms_state) <> Unlocked ->
  machine_steps slots m_init trace m ->
  no_valid_unlock_trace slots trace ->
  observe_dek m <> Some k.
Proof.
  intros slots trace m_init m k Hsafe_init Hnot_unlocked_init Hsteps Htrace.
  assert (Hnone := non_unlocked_no_auth_dek_confidentiality slots trace m_init m Hsafe_init Hnot_unlocked_init Hsteps Htrace).
  rewrite Hnone.
  discriminate.
Qed.

(** [SPEC]
    任意の安全な施錠状態から出発する一般化DEK平文非露出定理。 *)
Theorem locked_no_auth_dek_confidentiality_gen : forall (slots : KekSlots) (trace : list VaultEvent) (m_init m : VaultMachineState),
  SafeState m_init ->
  m_init.(vms_state) = Locked ->
  machine_steps slots m_init trace m ->
  no_valid_unlock_trace slots trace ->
  observe_dek m = None.
Proof.
  intros slots trace m_init m Hsafe_init Hlocked Hsteps Htrace.
  apply (non_unlocked_no_auth_dek_confidentiality slots trace m_init m Hsafe_init).
  - rewrite Hlocked. apply vault_state_locked_not_unlocked.
  - exact Hsteps.
  - exact Htrace.
Qed.

(** [SPEC]
    DEK平文非露出定理 (Data Plane Confidentiality Theorem)。
    施錠状態 (mkVaultMachineState Locked None) から出発して
    有効な認証イベントを経ずに遷移した任意のマシン状態 m においては、
    平文DEKが観測されることはなく、常に None が保たれることを保証する。 *)
Theorem locked_no_auth_dek_confidentiality : forall (slots : KekSlots) (trace : list VaultEvent) (m : VaultMachineState),
  machine_steps slots (mkVaultMachineState Locked None) trace m ->
  no_valid_unlock_trace slots trace ->
  observe_dek m = None.
Proof.
  intros slots trace m Hsteps Htrace.
  apply (non_unlocked_no_auth_dek_confidentiality slots trace (mkVaultMachineState Locked None) m safe_state_init vault_state_locked_not_unlocked Hsteps Htrace).
Qed.

(** [SPEC]
    DEK平文非露出定理の否定的帰結系 (Cannot Extract DEK Corollary)。
    施錠状態から有効な認証イベントを経ずに平文DEKを取り出すことは不可能であることを示す。 *)
Corollary locked_no_auth_cannot_extract_dek : forall (slots : KekSlots) (trace : list VaultEvent) (m : VaultMachineState) (k : DekBytes),
  machine_steps slots (mkVaultMachineState Locked None) trace m ->
  no_valid_unlock_trace slots trace ->
  observe_dek m <> Some k.
Proof.
  intros slots trace m k Hsteps Htrace.
  apply (non_unlocked_no_auth_cannot_extract_dek slots trace (mkVaultMachineState Locked None) m k safe_state_init vault_state_locked_not_unlocked Hsteps Htrace).
Qed.

(** [SPEC]
    構文的に解錠成功イベントを一切含まないトレースに対するDEK平文非露出定理の系。 *)
Corollary locked_syntax_no_auth_dek_confidentiality : forall (slots : KekSlots) (trace : list VaultEvent) (m : VaultMachineState),
  machine_steps slots (mkVaultMachineState Locked None) trace m ->
  no_unlock_success_trace trace ->
  observe_dek m = None.
Proof.
  intros slots trace m Hsteps Htrace.
  apply (locked_no_auth_dek_confidentiality slots trace m Hsteps).
  apply (no_unlock_success_implies_no_valid_unlock_trace slots trace Htrace).
Qed.

(** [SPEC]
    Zeroized状態から再初期化イベント (EventReset) を経ない単一ステップ遷移は存在しないことを示す補題。 *)
Lemma step_zeroized_no_reset_impossible : forall (slots : KekSlots) (ev : VaultEvent) (s' : VaultState),
  ev <> EventReset ->
  ~ step slots Zeroized ev s'.
Proof.
  intros slots ev s' Hnot_reset Hstep.
  apply step_zeroized_destinations in Hstep.
  destruct Hstep as [Hev Hs'].
  subst ev.
  apply Hnot_reset.
  reflexivity.
Qed.

(** [SPEC]
    イベント列に再初期化イベント (EventReset) が含まれないことを表す述語。 *)
Definition no_reset_trace (trace : list VaultEvent) : Prop :=
  Forall (fun ev => ev <> EventReset) trace.

(** [MODEL]
    イベント列に再初期化イベント (EventReset) が含まれないかを判定するブール関数。 *)
Definition no_reset_traceb (trace : list VaultEvent) : bool :=
  forallb (fun ev => match ev with EventReset => false | _ => true end) trace.

(** [SPEC]
    no_reset_traceb と no_reset_trace の同値性補題。 *)
Lemma no_reset_traceb_eq : forall (trace : list VaultEvent),
  no_reset_traceb trace = true <-> no_reset_trace trace.
Proof.
  intros trace.
  unfold no_reset_traceb, no_reset_trace.
  rewrite forallb_forall.
  rewrite Forall_forall.
  split; intros H ev Hin.
  - specialize (H ev Hin).
    destruct ev; try discriminate; intros Heq; discriminate.
  - specialize (H ev Hin).
    destruct ev; try reflexivity.
    exfalso. apply H. reflexivity.
Qed.

(** [SPEC]
    マスター鍵消去状態の完全滞留定理 (Strict Quarantine Theorem)。
    再初期化イベント (EventReset) を含まない任意の遷移列 (steps) において、
    マシンは Zeroized 状態から脱出できず、終点状態は Zeroized のまま留まることを保証する。 *)
Theorem steps_zeroized_no_reset_invariant : forall (slots : KekSlots) (trace : list VaultEvent) (s : VaultState),
  no_reset_trace trace ->
  steps slots Zeroized trace s ->
  s = Zeroized.
Proof.
  intros slots trace s Hno_reset Hsteps.
  inv Hsteps.
  - reflexivity.
  - apply step_zeroized_destinations in H.
    destruct H as [Hev Hs2].
    subst ev.
    inv Hno_reset.
    contradiction.
Qed.

(** [SPEC]
    マスター鍵消去状態からの非到達性定理 (Zeroized Reachability Soundness Theorem)。
    メモリゼロ消去状態 (Zeroized) から出発し、有効な解錠イベントを経由しない任意の遷移列 (steps) によって、
    解錠状態 (Unlocked) に到達することは不可能であることを保証する。 *)
Theorem zeroized_no_auth_unreachability : forall (slots : KekSlots) (trace : list VaultEvent) (s : VaultState),
  no_valid_unlock_trace slots trace ->
  steps slots Zeroized trace s ->
  s <> Unlocked.
Proof.
  intros slots trace s Htrace Hsteps.
  apply (steps_non_unlocked_invariant slots Zeroized trace s vault_state_zeroized_not_unlocked Htrace Hsteps).
Qed.

(** [SPEC]
    構文的に解錠成功イベントを一切含まないトレースに対する、マスター鍵消去状態からの非到達性定理の系。 *)
Corollary zeroized_syntax_no_auth_unreachability : forall (slots : KekSlots) (trace : list VaultEvent) (s : VaultState),
  no_unlock_success_trace trace ->
  steps slots Zeroized trace s ->
  s <> Unlocked.
Proof.
  intros slots trace s Htrace Hsteps.
  apply (zeroized_no_auth_unreachability slots trace s).
  - apply (no_unlock_success_implies_no_valid_unlock_trace slots trace Htrace).
  - exact Hsteps.
Qed.

(** [SPEC]
    マスター鍵消去状態におけるDEK平文非露出定理 (Zeroized Data Plane Confidentiality Theorem)。
    ゼロ消去状態 (mkVaultMachineState Zeroized None) から出発して
    有効な認証イベントを経ずに遷移した任意のマシン状態 m においては、
    平文DEKが観測されることはなく、常に None が保たれることを保証する。 *)
Theorem zeroized_no_auth_dek_confidentiality : forall (slots : KekSlots) (trace : list VaultEvent) (m : VaultMachineState),
  machine_steps slots (mkVaultMachineState Zeroized None) trace m ->
  no_valid_unlock_trace slots trace ->
  observe_dek m = None.
Proof.
  intros slots trace m Hsteps Htrace.
  assert (Hsafe_init : SafeState (mkVaultMachineState Zeroized None)) by (cbn; reflexivity).
  apply (non_unlocked_no_auth_dek_confidentiality slots trace (mkVaultMachineState Zeroized None) m Hsafe_init vault_state_zeroized_not_unlocked Hsteps Htrace).
Qed.

(** [SPEC]
    任意の安全なゼロ消去状態から出発する一般化DEK平文非露出定理。 *)
Theorem zeroized_no_auth_dek_confidentiality_gen : forall (slots : KekSlots) (trace : list VaultEvent) (m_init m : VaultMachineState),
  SafeState m_init ->
  m_init.(vms_state) = Zeroized ->
  machine_steps slots m_init trace m ->
  no_valid_unlock_trace slots trace ->
  observe_dek m = None.
Proof.
  intros slots trace m_init m Hsafe_init Hzeroized Hsteps Htrace.
  apply (non_unlocked_no_auth_dek_confidentiality slots trace m_init m Hsafe_init).
  - rewrite Hzeroized. apply vault_state_zeroized_not_unlocked.
  - exact Hsteps.
  - exact Htrace.
Qed.

(** [SPEC]
    マスター鍵消去状態におけるDEK平文非露出定理の否定的帰結系 (Cannot Extract DEK from Zeroized State Corollary)。
    ゼロ消去状態から有効な認証イベントを経ずに平文DEKを取り出すことは不可能であることを示す。 *)
Corollary zeroized_no_auth_cannot_extract_dek : forall (slots : KekSlots) (trace : list VaultEvent) (m : VaultMachineState) (k : DekBytes),
  machine_steps slots (mkVaultMachineState Zeroized None) trace m ->
  no_valid_unlock_trace slots trace ->
  observe_dek m <> Some k.
Proof.
  intros slots trace m k Hsteps Htrace.
  assert (Hsafe_init : SafeState (mkVaultMachineState Zeroized None)) by (cbn; reflexivity).
  apply (non_unlocked_no_auth_cannot_extract_dek slots trace (mkVaultMachineState Zeroized None) m k Hsafe_init vault_state_zeroized_not_unlocked Hsteps Htrace).
Qed.

(** [SPEC]
    構文的に解錠成功イベントを一切含まないトレースに対する、マスター鍵消去状態におけるDEK平文非露出定理の系。 *)
Corollary zeroized_syntax_no_auth_dek_confidentiality : forall (slots : KekSlots) (trace : list VaultEvent) (m : VaultMachineState),
  machine_steps slots (mkVaultMachineState Zeroized None) trace m ->
  no_unlock_success_trace trace ->
  observe_dek m = None.
Proof.
  intros slots trace m Hsteps Htrace.
  apply (zeroized_no_auth_dek_confidentiality slots trace m Hsteps).
  apply (no_unlock_success_implies_no_valid_unlock_trace slots trace Htrace).
Qed.

(** [SPEC]
    解錠状態到達における再初期化イベント必須性定理 (Reset Requirement for Unlocking Theorem)。
    Zeroized 状態から Unlocked 状態へ到達する任意の遷移トレースには、
    必ず EventReset イベントが含まれていなければならないことを保証する。 *)
Theorem steps_zeroized_to_unlocked_requires_reset : forall (slots : KekSlots) (trace : list VaultEvent),
  steps slots Zeroized trace Unlocked ->
  In EventReset trace.
Proof.
  intros slots trace Hsteps.
  destruct (in_dec vault_event_eq_dec EventReset trace) as [Hin | Hnot_in].
  - exact Hin.
  - exfalso.
    assert (Hno_reset : no_reset_trace trace).
    {
      unfold no_reset_trace.
      rewrite Forall_forall.
      intros ev Hin Heq.
      subst ev.
      apply Hnot_in.
      exact Hin.
    }
    assert (Heq := steps_zeroized_no_reset_invariant slots trace Unlocked Hno_reset Hsteps).
    discriminate Heq.
Qed.

(** [SPEC]
    非解錠状態から解錠状態への到達における認証イベント存在に関する一般化補題。
    非解錠状態 (s1 <> Unlocked) から Unlocked へ到達する任意の遷移列 steps には、
    健全なスロットに対する有効な解錠成功イベントが含まれていなければならないことを構成的に示す。 *)
Lemma steps_to_unlocked_requires_auth_gen : forall (slots : KekSlots) (s1 s2 : VaultState) (trace : list VaultEvent),
  steps slots s1 trace s2 ->
  s1 <> Unlocked ->
  s2 = Unlocked ->
  exists (id : SlotId), In (EventUnlockSuccess id) trace /\ slot_valid slots id.
Proof.
  intros slots s1 s2 trace Hsteps.
  induction Hsteps as [s | s_a s_b s_c ev tr Hstep Hsteps' IH].
  - intros Hs1 Hs2.
    subst s.
    exfalso. apply Hs1. reflexivity.
  - intros Hs_a Hs_c.
    destruct (vault_state_eq_dec s_b Unlocked) as [Heq_b | Hneq_b].
    + subst s_b.
      destruct s_a.
      * exfalso.
        apply (step_locked_to_unlocked_impossible slots ev Hstep).
      * apply step_unlocking_destinations in Hstep.
        destruct Hstep as [[id [Hev [Hdest Hval]]] | [Hev Hdest]].
        -- exists id.
           split.
           ++ left. exact Hev.
           ++ exact Hval.
        -- discriminate Hdest.
      * exfalso. apply Hs_a. reflexivity.
      * apply step_zeroized_destinations in Hstep.
        destruct Hstep as [Hev Hdest].
        discriminate Hdest.
    + specialize (IH Hneq_b Hs_c).
      destruct IH as [id [Hin Hval]].
      exists id.
      split.
      * right. exact Hin.
      * exact Hval.
Qed.

(** [SPEC]
    非解錠状態から解錠状態への到達における認証イベント存在補題。
    非解錠状態 (s1 <> Unlocked) から Unlocked へ到達する任意の遷移トレースには、
    健全なスロットに対する有効な解錠成功イベントが含まれていなければならないことを構成的に示す。 *)
Lemma steps_to_unlocked_requires_auth : forall (slots : KekSlots) (s1 : VaultState) (trace : list VaultEvent),
  s1 <> Unlocked ->
  steps slots s1 trace Unlocked ->
  exists (id : SlotId), In (EventUnlockSuccess id) trace /\ slot_valid slots id.
Proof.
  intros slots s1 trace Hs1 Hsteps.
  apply (steps_to_unlocked_requires_auth_gen slots s1 Unlocked trace Hsteps Hs1 eq_refl).
Qed.

(** [SPEC]
    マスター鍵消去状態から解錠状態到達における有効認証イベント必須性定理 (Authentication Requirement Theorem)。
    Zeroized 状態から Unlocked 状態へ到達する任意の遷移トレースには、
    健全なスロットに対する有効な解錠成功イベントが含まれていなければならないことを保証する。 *)
Theorem steps_zeroized_to_unlocked_requires_auth : forall (slots : KekSlots) (trace : list VaultEvent),
  steps slots Zeroized trace Unlocked ->
  exists (id : SlotId), In (EventUnlockSuccess id) trace /\ slot_valid slots id.
Proof.
  intros slots trace Hsteps.
  apply (steps_to_unlocked_requires_auth slots Zeroized trace vault_state_zeroized_not_unlocked Hsteps).
Qed.
