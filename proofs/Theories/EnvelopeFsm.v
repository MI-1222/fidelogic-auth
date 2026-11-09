(** * DEKライフサイクル状態機械 (FSM) モジュール。 *)
(** [SPEC]
    本モジュールはマルチスロット型エンベロープ暗号化における、
    DEK (Data Encryption Key) のライフサイクル状態および基本決定論述語を形式定義する。 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
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
    + destruct H as [H | [H | H]]; inversion H.
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
  inversion H1; subst; inversion H2; subst; reflexivity.
Qed.

(** [SPEC]
    Locked状態から任意の単一ステップ遷移によって直接Unlocked状態へ到達することは不可能であることを示す補題。 *)
Lemma step_locked_to_unlocked_impossible : forall (slots : KekSlots) (ev : VaultEvent),
  ~ step slots Locked ev Unlocked.
Proof.
  intros slots ev Hstep.
  inversion Hstep.
Qed.

(** [SPEC]
    Zeroized状態から任意の単一ステップ遷移によって直接Unlocked状態へ到達することは不可能であることを示す補題。 *)
Lemma step_zeroized_to_unlocked_impossible : forall (slots : KekSlots) (ev : VaultEvent),
  ~ step slots Zeroized ev Unlocked.
Proof.
  intros slots ev Hstep.
  inversion Hstep.
Qed.

(** [SPEC]
    EventUnlockSuccess による遷移が成立するためには、指定されたスロットが健全 (slot_valid) でなければならないことを示す補題。 *)
Lemma step_unlock_success_requires_valid : forall (slots : KekSlots) (id : SlotId) (s' : VaultState),
  step slots Unlocking (EventUnlockSuccess id) s' ->
  slot_valid slots id.
Proof.
  intros slots id s' Hstep.
  inversion Hstep as [ | id0 Hval | | | | ]; subst.
  exact Hval.
Qed.

(** [SPEC]
    EventStartUnlock による遷移が成立するためには、指定されたスロットIDが有効範囲内 (valid_slot_id) でなければならないことを示す補題。 *)
Lemma step_start_unlock_requires_valid_id : forall (slots : KekSlots) (id : SlotId) (s' : VaultState),
  step slots Locked (EventStartUnlock id) s' ->
  valid_slot_id id.
Proof.
  intros slots id s' Hstep.
  inversion Hstep as [ id0 Hval | | | | | ]; subst.
  exact Hval.
Qed.

(** [SPEC]
    Unlocked状態から退行する遷移は施錠 (EventLock) またはゼロ消去 (EventZeroize) のみであることを示す補題。 *)
Lemma step_unlocked_destinations : forall (slots : KekSlots) (ev : VaultEvent) (s' : VaultState),
  step slots Unlocked ev s' ->
  (ev = EventLock /\ s' = Locked) \/ (ev = EventZeroize /\ s' = Zeroized).
Proof.
  intros slots ev s' Hstep.
  inversion Hstep; subst.
  - left. split; reflexivity.
  - right. split; reflexivity.
Qed.

(** [SPEC]
    Locked状態からの遷移先は有効なスロットIDに対するEventStartUnlockによるUnlocking状態のみであることを示す補題。 *)
Lemma step_locked_destinations : forall (slots : KekSlots) (ev : VaultEvent) (s' : VaultState),
  step slots Locked ev s' ->
  exists (id : SlotId), ev = EventStartUnlock id /\ s' = Unlocking /\ valid_slot_id id.
Proof.
  intros slots ev s' Hstep.
  inversion Hstep as [ id0 Hval | | | | | ]; subst.
  exists id0.
  split; [reflexivity | split; [reflexivity | exact Hval]].
Qed.

(** [SPEC]
    Zeroized状態からの遷移先はEventResetによるLocked状態のみであることを示す補題。 *)
Lemma step_zeroized_destinations : forall (slots : KekSlots) (ev : VaultEvent) (s' : VaultState),
  step slots Zeroized ev s' ->
  ev = EventReset /\ s' = Locked.
Proof.
  intros slots ev s' Hstep.
  inversion Hstep; subst.
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
  inversion Hstep as [ | id0 Hval | | | | ]; subst.
  - left. exists id0. split; [reflexivity | split; [reflexivity | exact Hval]].
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

