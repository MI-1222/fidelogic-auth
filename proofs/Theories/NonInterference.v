(** * 情報流非干渉性 (Non-Interference) および2レベルセキュリティ型付けモジュール。 *)
(** [SPEC]
    本モジュールは暗号化Vaultおよび認証プロトコルにおける情報漏洩を防ぐため、
    情報流制御 (Information Flow Control: IFC) に基づく2レベルセキュリティ格子 (Low / High)、
    高位機密 (平文データ・マスター鍵・存在フラグ) と低位観測値 (エラー型・メッセージ長・公開ヘッダー) の型付け、
    低位観測射影関数、および低位等価関係 (Low-Equivalence: ≈_L) を形式定義し、
    その代数的健全性 (同値関係・束構造・決定可能性) を純粋直観主義論理の枠組みで証明する。 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

From Fidelogic Require Import Tactics.
From Fidelogic.Theories Require Import FidelogicCore.
Import FidelogicCore.
From Fidelogic.Theories Require Import EnvelopeFsm.

Local Open Scope Z_scope.

(** -------------------------------------------------------------------------
    1. 2レベルセキュリティ格子
    ------------------------------------------------------------------------- *)

(** [MODEL]
    2レベルセキュリティ格子の機密レベルを表す帰納型。
    Low (低位: 公開・攻撃者観測可能) と High (高位: 機密・漏洩禁止) の2値を定義する。 *)
Inductive SecLevel : Type :=
  | Low : SecLevel
  | High : SecLevel.

(** [SPEC]
    SecLevel 間の決定可能等価性補題。 *)
Lemma sec_level_eq_dec : forall (l1 l2 : SecLevel), {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
Qed.

(** [MODEL]
    SecLevel 間のブール値等価判定関数。 *)
Definition sec_level_eqb (l1 l2 : SecLevel) : bool :=
  match l1, l2 with
  | Low, Low => true
  | High, High => true
  | _, _ => false
  end.

(** [SPEC]
    sec_level_eqb の反射性補題。 *)
Lemma sec_level_eqb_refl : forall (l : SecLevel),
  sec_level_eqb l l = true.
Proof.
  destruct l; reflexivity.
Qed.

(** [SPEC]
    sec_level_eqb と等号命題の同値性補題。 *)
Lemma sec_level_eqb_eq : forall (l1 l2 : SecLevel),
  sec_level_eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros l1 l2.
  destruct l1; destruct l2; split; intros H;
    try reflexivity; try discriminate H; inv H.
Qed.

(** [SPEC]
    SecLevel の有限網羅性補題。 *)
Lemma sec_level_cases : forall (l : SecLevel),
  l = Low \/ l = High.
Proof.
  destruct l; [left | right]; reflexivity.
Qed.

(** [SPEC]
    Low と High の排他性補題。 *)
Lemma sec_level_low_not_high : Low <> High.
Proof.
  discriminate.
Qed.

Lemma sec_level_high_not_low : High <> Low.
Proof.
  discriminate.
Qed.

(** [MODEL]
    情報流の許容順序関係述語 (Information Flow Ordering: <=_sec)。
    Low <= Low, Low <= High, High <= High を許可し、High <= Low (機密漏洩) を禁止する。 *)
Inductive sec_le : SecLevel -> SecLevel -> Prop :=
  | SecLe_Low_Low : sec_le Low Low
  | SecLe_Low_High : sec_le Low High
  | SecLe_High_High : sec_le High High.

(** [MODEL]
    情報流順序のブール値判定関数。 *)
Definition sec_leb (l1 l2 : SecLevel) : bool :=
  match l1, l2 with
  | Low, _ => true
  | High, High => true
  | High, Low => false
  end.

(** [SPEC]
    sec_leb と sec_le の Reflection 同値性補題。 *)
Lemma sec_leb_spec : forall (l1 l2 : SecLevel),
  sec_leb l1 l2 = true <-> sec_le l1 l2.
Proof.
  intros l1 l2.
  destruct l1; destruct l2; split; intros H;
    try reflexivity;
    try discriminate H;
    try constructor;
    try (inv H; fail).
Qed.

(** [SPEC]
    sec_le の決定可能性補題。 *)
Lemma sec_le_dec : forall (l1 l2 : SecLevel),
  {sec_le l1 l2} + {~ sec_le l1 l2}.
Proof.
  intros l1 l2.
  destruct (sec_leb l1 l2) eqn:E.
  - left. apply sec_leb_spec. exact E.
  - right. intros H. apply sec_leb_spec in H. rewrite H in E. discriminate.
Qed.

(** [SPEC]
    情報流順序の反射律。 *)
Lemma sec_le_refl : forall (l : SecLevel),
  sec_le l l.
Proof.
  destruct l; constructor.
Qed.

(** [SPEC]
    情報流順序の推移律。 *)
Lemma sec_le_trans : forall (l1 l2 l3 : SecLevel),
  sec_le l1 l2 -> sec_le l2 l3 -> sec_le l1 l3.
Proof.
  intros l1 l2 l3 H12 H23.
  destruct l1; destruct l2; destruct l3;
    try constructor;
    try (inv H12; fail);
    try (inv H23; fail).
Qed.

(** [SPEC]
    情報流順序の反対称律。 *)
Lemma sec_le_antisym : forall (l1 l2 : SecLevel),
  sec_le l1 l2 -> sec_le l2 l1 -> l1 = l2.
Proof.
  intros l1 l2 H12 H21.
  destruct l1; destruct l2;
    try reflexivity;
    try (inv H12; fail);
    try (inv H21; fail).
Qed.

(** [SPEC]
    Low は最小元 (Bottom) であることの補題。 *)
Lemma sec_le_low_bottom : forall (l : SecLevel),
  sec_le Low l.
Proof.
  destruct l; constructor.
Qed.

(** [SPEC]
    High は最大元 (Top) であることの補題。 *)
Lemma sec_le_high_top : forall (l : SecLevel),
  sec_le l High.
Proof.
  destruct l; constructor.
Qed.

(** [SPEC]
    High から Low への情報流不成立補題 (機密流出禁止)。 *)
Lemma sec_le_high_low_false : ~ sec_le High Low.
Proof.
  intros H. inv H.
Qed.

(** [MODEL]
    2レベル格子の結合演算 (Join / 最小上界 / Least Upper Bound)。 *)
Definition sec_join (l1 l2 : SecLevel) : SecLevel :=
  match l1, l2 with
  | High, _ => High
  | _, High => High
  | Low, Low => Low
  end.

(** [MODEL]
    2レベル格子の交わり演算 (Meet / 最大下界 / Greatest Lower Bound)。 *)
Definition sec_meet (l1 l2 : SecLevel) : SecLevel :=
  match l1, l2 with
  | Low, _ => Low
  | _, Low => Low
  | High, High => High
  end.

(** [SPEC]
    sec_join の可換性補題。 *)
Lemma sec_join_comm : forall (l1 l2 : SecLevel),
  sec_join l1 l2 = sec_join l2 l1.
Proof.
  destruct l1; destruct l2; reflexivity.
Qed.

(** [SPEC]
    sec_meet の可換性補題。 *)
Lemma sec_meet_comm : forall (l1 l2 : SecLevel),
  sec_meet l1 l2 = sec_meet l2 l1.
Proof.
  destruct l1; destruct l2; reflexivity.
Qed.

(** [SPEC]
    sec_join の結合性補題。 *)
Lemma sec_join_assoc : forall (l1 l2 l3 : SecLevel),
  sec_join l1 (sec_join l2 l3) = sec_join (sec_join l1 l2) l3.
Proof.
  destruct l1; destruct l2; destruct l3; reflexivity.
Qed.

(** [SPEC]
    sec_meet の結合性補題。 *)
Lemma sec_meet_assoc : forall (l1 l2 l3 : SecLevel),
  sec_meet l1 (sec_meet l2 l3) = sec_meet (sec_meet l1 l2) l3.
Proof.
  destruct l1; destruct l2; destruct l3; reflexivity.
Qed.

(** [SPEC]
    sec_join の冪等性補題。 *)
Lemma sec_join_idemp : forall (l : SecLevel),
  sec_join l l = l.
Proof.
  destruct l; reflexivity.
Qed.

(** [SPEC]
    sec_meet の冪等性補題。 *)
Lemma sec_meet_idemp : forall (l : SecLevel),
  sec_meet l l = l.
Proof.
  destruct l; reflexivity.
Qed.

(** [SPEC]
    sec_join と sec_meet の吸収律補題。 *)
Lemma sec_join_meet_absorb : forall (l1 l2 : SecLevel),
  sec_join l1 (sec_meet l1 l2) = l1.
Proof.
  destruct l1; destruct l2; reflexivity.
Qed.

Lemma sec_meet_join_absorb : forall (l1 l2 : SecLevel),
  sec_meet l1 (sec_join l1 l2) = l1.
Proof.
  destruct l1; destruct l2; reflexivity.
Qed.

(** [SPEC]
    sec_join は左引数の上界である補題。 *)
Lemma sec_join_ub_left : forall (l1 l2 : SecLevel),
  sec_le l1 (sec_join l1 l2).
Proof.
  destruct l1; destruct l2; constructor.
Qed.

(** [SPEC]
    sec_join は右引数の上界である補題。 *)
Lemma sec_join_ub_right : forall (l1 l2 : SecLevel),
  sec_le l2 (sec_join l1 l2).
Proof.
  destruct l1; destruct l2; constructor.
Qed.

(** [SPEC]
    sec_join は最小上界である補題。 *)
Lemma sec_join_least : forall (l1 l2 l3 : SecLevel),
  sec_le l1 l3 -> sec_le l2 l3 -> sec_le (sec_join l1 l2) l3.
Proof.
  intros l1 l2 l3 H1 H2.
  destruct l1; destruct l2; destruct l3;
    try constructor;
    try (inv H1; fail);
    try (inv H2; fail).
Qed.

(** [SPEC]
    sec_meet は左引数の下界である補題。 *)
Lemma sec_meet_lb_left : forall (l1 l2 : SecLevel),
  sec_le (sec_meet l1 l2) l1.
Proof.
  destruct l1; destruct l2; constructor.
Qed.

(** [SPEC]
    sec_meet は右引数の下界である補題。 *)
Lemma sec_meet_lb_right : forall (l1 l2 : SecLevel),
  sec_le (sec_meet l1 l2) l2.
Proof.
  destruct l1; destruct l2; constructor.
Qed.

(** [SPEC]
    sec_meet は最大下界である補題。 *)
Lemma sec_meet_greatest : forall (l1 l2 l3 : SecLevel),
  sec_le l3 l1 -> sec_le l3 l2 -> sec_le l3 (sec_meet l1 l2).
Proof.
  intros l1 l2 l3 H1 H2.
  destruct l1; destruct l2; destruct l3;
    try constructor;
    try (inv H1; fail);
    try (inv H2; fail).
Qed.


(** -------------------------------------------------------------------------
    2. ラベル付き値・セキュリティ型付け
    ------------------------------------------------------------------------- *)

(** [MODEL]
    セキュリティレベルが付与されたラベル付き値。 *)
Record SecVal (A : Type) : Type := mkSecVal {
  sec_val_level : SecLevel;
  sec_val_data : A;
}.

Arguments mkSecVal {A}.
Arguments sec_val_level {A}.
Arguments sec_val_data {A}.

(** [MODEL]
    値が指定のセキュリティレベルを持つことを表す型付け述語。 *)
Definition has_sec_level {A : Type} (lvl : SecLevel) (v : SecVal A) : Prop :=
  sec_val_level v = lvl.

(** [MODEL]
    ラベル付き値がターゲットレベルへ流出可能であるかを表す情報流述語。 *)
Definition flows_to {A : Type} (v : SecVal A) (target_lvl : SecLevel) : Prop :=
  sec_le (sec_val_level v) target_lvl.

(** [SPEC]
    自身のセキュリティレベルへの情報流は常に成立する補題。 *)
Lemma flows_to_self : forall {A : Type} (v : SecVal A),
  flows_to v (sec_val_level v).
Proof.
  intros A v.
  unfold flows_to.
  apply sec_le_refl.
Qed.

(** [SPEC]
    High レベルへの情報流は常に許可される補題。 *)
Lemma flows_to_high : forall {A : Type} (v : SecVal A),
  flows_to v High.
Proof.
  intros A v.
  unfold flows_to.
  apply sec_le_high_top.
Qed.

(** [SPEC]
    Low ラベル付き値は任意レベルへ情報流が可能である補題。 *)
Lemma low_val_flows_to_any : forall {A : Type} (v : SecVal A),
  sec_val_level v = Low ->
  forall (l : SecLevel), flows_to v l.
Proof.
  intros A v H l.
  unfold flows_to.
  rewrite H.
  apply sec_le_low_bottom.
Qed.

(** [SPEC]
    High ラベル付き値は Low レベルへ流出不可能である補題 (機密保持保証)。 *)
Lemma high_val_cannot_flow_to_low : forall {A : Type} (v : SecVal A),
  sec_val_level v = High ->
  ~ flows_to v Low.
Proof.
  intros A v H Hflow.
  unfold flows_to in Hflow.
  rewrite H in Hflow.
  apply sec_le_high_low_false in Hflow.
  exact Hflow.
Qed.


(** -------------------------------------------------------------------------
    3. 機密データ・低位観測値・状態モデル (Domain Models)
    ------------------------------------------------------------------------- *)

(** [MODEL]
    高位機密データ構造体 (HighSecret)。
    外部への漏洩が厳格に禁止される平文・マスター鍵・秘密存在フラグを保持する。 *)
Record HighSecret : Type := mkHighSecret {
  sec_master_key : option DekBytes;
  sec_plaintext : list Z;
  sec_user_exists : bool;
  sec_entry_exists : bool;
}.

(** [SPEC]
    HighSecret 間の決定可能等価性補題。 *)
Lemma high_secret_eq_dec : forall (h1 h2 : HighSecret),
  {h1 = h2} + {h1 <> h2}.
Proof.
  decide equality.
  - apply bool_dec.
  - apply bool_dec.
  - apply list_eq_dec, Z.eq_dec.
  - decide equality; apply list_eq_dec, Z.eq_dec.
Qed.

(** [SPEC]
    tlv_VaultError_t 間の決定可能等価性補題。 *)
Lemma tlv_vault_error_eq_dec : forall (e1 e2 : tlv_VaultError_t),
  {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
Qed.

(** [MODEL]
    公開Vaultヘッダーの純粋メタデータ構造体 (LowHeader)。
    マジックバイト、バージョン番号、暗号スイート識別子を整数型 Z で表現し、
    外部公理への依存を排除して完全な純粋直観主義モデルを担保する。 *)
Record LowHeader : Type := mkLowHeader {
  hdr_magic : Z;
  hdr_version : Z;
  hdr_cipher_suite : Z;
}.

(** [SPEC]
    LowHeader 間の決定可能等価性補題。 *)
Lemma low_header_eq_dec : forall (h1 h2 : LowHeader),
  {h1 = h2} + {h1 <> h2}.
Proof.
  decide equality; apply Z.eq_dec.
Qed.

(** [SPEC]
    option 型に対する決定可能等価性補題。 *)
Lemma option_eq_dec : forall {A : Type} (eq_dec_A : forall (x y : A), {x = y} + {x <> y}) (o1 o2 : option A),
  {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality.
Qed.

(** [MODEL]
    低位観測値構造体 (LowObservation)。
    通信トラフィックやAPI応答から攻撃者・外部観測者が直接観測可能な情報を表す。 *)
Record LowObservation : Type := mkLowObservation {
  obs_error : option tlv_VaultError_t;
  obs_length : nat;
  obs_header : LowHeader;
  obs_slot_id : option SlotId;
}.

(** [SPEC]
    LowObservation 間の決定可能等価性補題。 *)
Lemma low_observation_eq_dec : forall (o1 o2 : LowObservation),
  {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality.
  - decide equality; apply Nat.eq_dec.
  - apply low_header_eq_dec.
  - apply Nat.eq_dec.
  - decide equality; apply tlv_vault_error_eq_dec.
Qed.

(** [MODEL]
    低位公開入力パラメータ構造体 (LowPublic)。 *)
Record LowPublic : Type := mkLowPublic {
  pub_header : LowHeader;
  pub_slot_id : option SlotId;
  pub_req_length : nat;
}.

(** [MODEL]
    Vaultマシンの統合セキュリティ状態構造体 (VaultSecurityState)。 *)
Record VaultSecurityState : Type := mkVaultSecurityState {
  state_high : HighSecret;
  state_low_obs : LowObservation;
}.

(** [SPEC]
    VaultSecurityState 間の決定可能等価性補題。 *)
Lemma vault_security_state_eq_dec : forall (s1 s2 : VaultSecurityState),
  {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
  - apply low_observation_eq_dec.
  - apply high_secret_eq_dec.
Qed.

(** [MODEL]
    Vaultマシンの入力セキュリティモデル (VaultSecurityInput)。 *)
Record VaultSecurityInput : Type := mkVaultSecurityInput {
  input_high : HighSecret;
  input_public : LowPublic;
}.


(** -------------------------------------------------------------------------
    4. 低位観測射影と低位等価性 (Low-Equivalence: ≈_L)
    ------------------------------------------------------------------------- *)

(** [MODEL]
    VaultSecurityState から低位観測値を抽出する射影関数。
    高位機密 (鍵・平文・存在フラグ) は完全に捨象される。 *)
Definition observe_low (s : VaultSecurityState) : LowObservation :=
  state_low_obs s.

(** [MODEL]
    2つの LowObservation が低位観測者にとって完全に一致することを表す等価述語。 *)
Definition low_obs_eq (o1 o2 : LowObservation) : Prop :=
  obs_error o1 = obs_error o2 /\
  obs_length o1 = obs_length o2 /\
  obs_header o1 = obs_header o2 /\
  obs_slot_id o1 = obs_slot_id o2.

(** [MODEL]
    2つの状態が低位観測者にとって区別不能であることを表す低位等価関係 (Low-Equivalence: ≈_L)。 *)
Definition low_equiv (s1 s2 : VaultSecurityState) : Prop :=
  low_obs_eq (observe_low s1) (observe_low s2).

(** [SPEC]
    low_obs_eq の反射性補題。 *)
Lemma low_obs_eq_refl : forall (o : LowObservation),
  low_obs_eq o o.
Proof.
  intros o.
  unfold low_obs_eq.
  repeat split; reflexivity.
Qed.

(** [SPEC]
    low_obs_eq の対称性補題。 *)
Lemma low_obs_eq_sym : forall (o1 o2 : LowObservation),
  low_obs_eq o1 o2 -> low_obs_eq o2 o1.
Proof.
  intros o1 o2 H.
  unfold low_obs_eq in *.
  destruct H as [H1 [H2 [H3 H4]]].
  repeat split; symmetry; assumption.
Qed.

(** [SPEC]
    low_obs_eq の推移性補題。 *)
Lemma low_obs_eq_trans : forall (o1 o2 o3 : LowObservation),
  low_obs_eq o1 o2 -> low_obs_eq o2 o3 -> low_obs_eq o1 o3.
Proof.
  intros o1 o2 o3 H12 H23.
  unfold low_obs_eq in *.
  destruct H12 as [H12_1 [H12_2 [H12_3 H12_4]]].
  destruct H23 as [H23_1 [H23_2 [H23_3 H23_4]]].
  repeat split; etransitivity; eassumption.
Qed.

(** [SPEC]
    low_obs_eq と構文的等号の一致性補題。 *)
Lemma low_obs_eq_iff_eq : forall (o1 o2 : LowObservation),
  low_obs_eq o1 o2 <-> o1 = o2.
Proof.
  intros [e1 l1 h1 s1] [e2 l2 h2 s2].
  split.
  - intros [H1 [H2 [H3 H4]]].
    simpl in *.
    subst.
    reflexivity.
  - intros H.
    inv H.
    apply low_obs_eq_refl.
Qed.

(** [SPEC]
    low_obs_eq の決定可能性補題。 *)
Lemma low_obs_eq_dec : forall (o1 o2 : LowObservation),
  {low_obs_eq o1 o2} + {~ low_obs_eq o1 o2}.
Proof.
  intros o1 o2.
  destruct (low_observation_eq_dec o1 o2) as [Heq | Hneq].
  - subst. left. apply low_obs_eq_refl.
  - right. intros H. apply Hneq. apply low_obs_eq_iff_eq. exact H.
Qed.

(** [SPEC]
    低位等価関係 (low_equiv) の反射律。 *)
Lemma low_equiv_refl : forall (s : VaultSecurityState),
  low_equiv s s.
Proof.
  intros s.
  unfold low_equiv.
  apply low_obs_eq_refl.
Qed.

(** [SPEC]
    低位等価関係 (low_equiv) の対称律。 *)
Lemma low_equiv_sym : forall (s1 s2 : VaultSecurityState),
  low_equiv s1 s2 -> low_equiv s2 s1.
Proof.
  intros s1 s2 H.
  unfold low_equiv in *.
  apply low_obs_eq_sym.
  exact H.
Qed.

(** [SPEC]
    低位等価関係 (low_equiv) の推移律。 *)
Lemma low_equiv_trans : forall (s1 s2 s3 : VaultSecurityState),
  low_equiv s1 s2 -> low_equiv s2 s3 -> low_equiv s1 s3.
Proof.
  intros s1 s2 s3 H12 H23.
  unfold low_equiv in *.
  eapply low_obs_eq_trans; eassumption.
Qed.

(** [SPEC]
    low_equiv と射影結果の構文的等号の同値性補題。 *)
Lemma low_equiv_iff_obs_eq : forall (s1 s2 : VaultSecurityState),
  low_equiv s1 s2 <-> observe_low s1 = observe_low s2.
Proof.
  intros s1 s2.
  unfold low_equiv.
  apply low_obs_eq_iff_eq.
Qed.

(** [SPEC]
    low_equiv の決定可能性補題。 *)
Lemma low_equiv_dec : forall (s1 s2 : VaultSecurityState),
  {low_equiv s1 s2} + {~ low_equiv s1 s2}.
Proof.
  intros s1 s2.
  unfold low_equiv.
  apply low_obs_eq_dec.
Qed.


(** -------------------------------------------------------------------------
    5. パディングモデルと機密情報流非干渉性基礎補題
    ------------------------------------------------------------------------- *)

(** [MODEL]
    固定長パディング (Bucket Padding) の計算モデル。
    メッセージ長を bucket_size の倍数境界に切り上げる。 *)
Definition pad_to_bucket (bucket_size : nat) (len : nat) : nat :=
  match bucket_size with
  | O => len
  | S _ => (((len + bucket_size - 1) / bucket_size) * bucket_size)%nat
  end.

(** [SPEC]
    パディングサイズが 0 の場合は元の長さを維持する補題。 *)
Lemma pad_to_bucket_zero : forall (len : nat),
  pad_to_bucket 0 len = len.
Proof.
  intros len.
  reflexivity.
Qed.

(** [SPEC]
    同一バケット境界内の任意の長さに対するパディング値決定補題。
    k * bucket_size < len <= (k + 1) * bucket_size を満たすとき、
    パディング結果は正確に (k + 1) * bucket_size となる。 *)
Lemma pad_to_bucket_step : forall (bucket_size k len : nat),
  (bucket_size > 0)%nat ->
  (k * bucket_size < len)%nat ->
  (len <= (k + 1) * bucket_size)%nat ->
  pad_to_bucket bucket_size len = ((k + 1) * bucket_size)%nat.
Proof.
  intros bucket_size k len Hbs Hlow Hhigh.
  destruct bucket_size as [| b]; [lia |].
  unfold pad_to_bucket.
  assert (Hdiv: ((len + S b - 1) / S b = k + 1)%nat).
  {
    symmetry.
    apply Nat.div_unique with (r := (len + S b - 1 - (k + 1) * S b)%nat); lia.
  }
  rewrite Hdiv.
  reflexivity.
Qed.

(** [SPEC]
    同一バケット境界に収まる2つの長さに対するパディング長一致補題。
    len1, len2 が同一のバケット区間 (k * bucket_size, (k + 1) * bucket_size] に収まるならば、
    パディング後の長さは完全に一致する。 *)
Lemma pad_to_bucket_equal : forall (bucket_size k len1 len2 : nat),
  (bucket_size > 0)%nat ->
  (k * bucket_size < len1)%nat ->
  (len1 <= (k + 1) * bucket_size)%nat ->
  (k * bucket_size < len2)%nat ->
  (len2 <= (k + 1) * bucket_size)%nat ->
  pad_to_bucket bucket_size len1 = pad_to_bucket bucket_size len2.
Proof.
  intros bucket_size k len1 len2 Hbs Hlow1 Hhigh1 Hlow2 Hhigh2.
  rewrite (pad_to_bucket_step bucket_size k len1); try assumption.
  rewrite (pad_to_bucket_step bucket_size k len2); try assumption.
  reflexivity.
Qed.

(** [SPEC]
    第1バケット区間 (0 < len <= bucket_size) におけるパディング長一致系。 *)
Corollary pad_to_bucket_first_bucket_equal : forall (bucket_size len1 len2 : nat),
  (bucket_size > 0)%nat ->
  (len1 > 0)%nat ->
  (len1 <= bucket_size)%nat ->
  (len2 > 0)%nat ->
  (len2 <= bucket_size)%nat ->
  pad_to_bucket bucket_size len1 = pad_to_bucket bucket_size len2.
Proof.
  intros bucket_size len1 len2 Hbs Hlow1 Hhigh1 Hlow2 Hhigh2.
  apply (pad_to_bucket_equal bucket_size 0 len1 len2); lia.
Qed.

(** [SPEC]
    高位機密の独立性補題:
    状態 s1, s2 において高位機密 (HighSecret) の内容が任意に異なっていても、
    低位観測値 (LowObservation) が一致していれば低位同値 (s1 ≈_L s2) が成立する。 *)
Lemma high_secrets_independent_of_low_obs : forall (h1 h2 : HighSecret) (obs : LowObservation),
  low_equiv (mkVaultSecurityState h1 obs) (mkVaultSecurityState h2 obs).
Proof.
  intros h1 h2 obs.
  unfold low_equiv, observe_low.
  simpl.
  apply low_obs_eq_refl.
Qed.

(** [SPEC]
    ユーザー存在フラグに関する低位非干渉性基礎補題:
    ユーザーが存在する場合 (sec_user_exists = true) と非存在の場合 (sec_user_exists = false) であっても、
    低位観測値が同一であれば低位観測者には区別不能である。 *)
Lemma user_existence_low_equiv : forall (k1 k2 : option DekBytes) (p1 p2 : list Z) (e1 e2 : bool) (obs : LowObservation),
  low_equiv
    (mkVaultSecurityState (mkHighSecret k1 p1 true e1) obs)
    (mkVaultSecurityState (mkHighSecret k2 p2 false e2) obs).
Proof.
  intros.
  apply high_secrets_independent_of_low_obs.
Qed.

(** [SPEC]
    エントリ存在フラグに関する低位非干渉性基礎補題:
    エントリが存在する場合と存在しない場合であっても、低位観測値が同一であれば区別不能である。 *)
Lemma entry_existence_low_equiv : forall (k1 k2 : option DekBytes) (p1 p2 : list Z) (u1 u2 : bool) (obs : LowObservation),
  low_equiv
    (mkVaultSecurityState (mkHighSecret k1 p1 u1 true) obs)
    (mkVaultSecurityState (mkHighSecret k2 p2 u2 false) obs).
Proof.
  intros.
  apply high_secrets_independent_of_low_obs.
Qed.

(** [SPEC]
    マスター鍵素材に関する低位非干渉性基礎補題:
    有効なマスター鍵が存在する場合と存在しない場合 (または異なる鍵) であっても、
    低位観測値が同一であれば区別不能である。 *)
Lemma master_key_low_equiv : forall (k1 k2 : option DekBytes) (p1 p2 : list Z) (u1 u2 e1 e2 : bool) (obs : LowObservation),
  low_equiv
    (mkVaultSecurityState (mkHighSecret k1 p1 u1 e1) obs)
    (mkVaultSecurityState (mkHighSecret k2 p2 u2 e2) obs).
Proof.
  intros.
  apply high_secrets_independent_of_low_obs.
Qed.

(** [SPEC]
    平文データに関する低位非干渉性基礎補題:
    平文の内容や長さが異なっていても、パディング等により同一の低位観測値が生成されるならば区別不能である。 *)
Lemma plaintext_low_equiv : forall (k1 k2 : option DekBytes) (p1 p2 : list Z) (u1 u2 e1 e2 : bool) (obs : LowObservation),
  low_equiv
    (mkVaultSecurityState (mkHighSecret k1 p1 u1 e1) obs)
    (mkVaultSecurityState (mkHighSecret k2 p2 u2 e2) obs).
Proof.
  intros.
  apply high_secrets_independent_of_low_obs.
Qed.


(** -------------------------------------------------------------------------
    6. 防護的評価モデルと非干渉性定理 (Non-Interference)
    ------------------------------------------------------------------------- *)

(** [SPEC]
    LowPublic 間の決定可能等価性補題。 *)
Lemma low_public_eq_dec : forall (p1 p2 : LowPublic),
  {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - decide equality; apply Nat.eq_dec.
  - apply low_header_eq_dec.
Qed.

(** [MODEL]
    入力セキュリティモデル (VaultSecurityInput) における低位公開入力の等価述語。
    攻撃者・外部観測者が制御・観測可能な公開パラメータ (LowPublic) が一致することを表す。 *)
Definition low_input_equiv (inp1 inp2 : VaultSecurityInput) : Prop :=
  input_public inp1 = input_public inp2.

(** [SPEC]
    low_input_equiv の反射性補題。 *)
Lemma low_input_equiv_refl : forall (inp : VaultSecurityInput),
  low_input_equiv inp inp.
Proof.
  intros inp.
  unfold low_input_equiv.
  reflexivity.
Qed.

(** [SPEC]
    low_input_equiv の対称性補題。 *)
Lemma low_input_equiv_sym : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  low_input_equiv inp2 inp1.
Proof.
  intros inp1 inp2 H.
  unfold low_input_equiv in *.
  symmetry.
  exact H.
Qed.

(** [SPEC]
    low_input_equiv の推移性補題。 *)
Lemma low_input_equiv_trans : forall (inp1 inp2 inp3 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  low_input_equiv inp2 inp3 ->
  low_input_equiv inp1 inp3.
Proof.
  intros inp1 inp2 inp3 H12 H23.
  unfold low_input_equiv in *.
  rewrite H12.
  exact H23.
Qed.

(** [SPEC]
    low_input_equiv の決定可能性補題。 *)
Lemma low_input_equiv_dec : forall (inp1 inp2 : VaultSecurityInput),
  {low_input_equiv inp1 inp2} + {~ low_input_equiv inp1 inp2}.
Proof.
  intros inp1 inp2.
  unfold low_input_equiv.
  apply low_public_eq_dec.
Qed.

(** [SPEC]
    公開入力等号から low_input_equiv を導出する補題。 *)
Lemma low_input_equiv_intro : forall (inp1 inp2 : VaultSecurityInput),
  input_public inp1 = input_public inp2 ->
  low_input_equiv inp1 inp2.
Proof.
  intros inp1 inp2 H.
  exact H.
Qed.

(** [MODEL]
    ユーザー存在摂動関係述語 (User Existence Perturbation)。
    マスター鍵、平文、およびエントリ存在フラグが同一であり、
    ユーザー存在フラグ (sec_user_exists) の真偽値のみが異なり得る入力の組を表す。 *)
Definition user_perturbed (h1 h2 : HighSecret) : Prop :=
  sec_master_key h1 = sec_master_key h2 /\
  sec_plaintext h1 = sec_plaintext h2 /\
  sec_entry_exists h1 = sec_entry_exists h2.

(** [SPEC]
    user_perturbed の反射性補題。 *)
Lemma user_perturbed_refl : forall (h : HighSecret),
  user_perturbed h h.
Proof.
  intros h.
  unfold user_perturbed.
  repeat split; reflexivity.
Qed.

(** [SPEC]
    user_perturbed の対称性補題。 *)
Lemma user_perturbed_sym : forall (h1 h2 : HighSecret),
  user_perturbed h1 h2 ->
  user_perturbed h2 h1.
Proof.
  intros h1 h2 [Hk [Hp He]].
  unfold user_perturbed.
  repeat split; symmetry; assumption.
Qed.

(** [MODEL]
    エントリ存在摂動関係述語 (Entry Existence Perturbation)。
    マスター鍵、ユーザー存在フラグが同一であり、
    エントリ存在フラグ (sec_entry_exists) の真偽値のみが異なり得る入力の組を表す。 *)
Definition entry_perturbed (h1 h2 : HighSecret) : Prop :=
  sec_master_key h1 = sec_master_key h2 /\
  sec_user_exists h1 = sec_user_exists h2.

(** [SPEC]
    entry_perturbed の反射性補題。 *)
Lemma entry_perturbed_refl : forall (h : HighSecret),
  entry_perturbed h h.
Proof.
  intros h.
  unfold entry_perturbed.
  split; reflexivity.
Qed.

(** [SPEC]
    entry_perturbed の対称性補題。 *)
Lemma entry_perturbed_sym : forall (h1 h2 : HighSecret),
  entry_perturbed h1 h2 ->
  entry_perturbed h2 h1.
Proof.
  intros h1 h2 [Hk Hu].
  unfold entry_perturbed.
  split; symmetry; assumption.
Qed.

(** [MODEL]
    防護的評価におけるデフォルトダミーペイロード長 (バイト数)。 *)
Definition default_dummy_len : nat := 32%nat.

(** [MODEL]
    防護的ユーザー認証評価関数 (eval_auth)。
    ユーザー存在の有無 (sec_user_exists) およびマスター鍵の有無を実際に評価・分岐するが、
    防護的マスキングにより、低位観測値には一様のエラー型 (UnexpectedEof によるマスキング)
    および要求された公開バケット長にパディングされたレスポンス長を出力し、ユーザー列挙オラクルを排除する。 *)
Definition eval_auth (inp : VaultSecurityInput) : LowObservation :=
  let (err, raw_len) :=
    if sec_user_exists (input_high inp)
    then
      match sec_master_key (input_high inp) with
      | Some _ => (Some Tlv_VaultError_UnexpectedEof, default_dummy_len)
      | None   => (Some Tlv_VaultError_UnexpectedEof, default_dummy_len)
      end
    else
      (Some Tlv_VaultError_UnexpectedEof, default_dummy_len)
  in
  mkLowObservation
    err
    (pad_to_bucket (pub_req_length (input_public inp)) raw_len)
    (pub_header (input_public inp))
    (pub_slot_id (input_public inp)).

(** [MODEL]
    ダミー長を考慮したエントリ照会評価関数 (eval_entry_lookup)。
    エントリが存在する場合は平文長、非存在時は固定ダミー長を採用し、
    指定バケットサイズにパディングしたレスポンス長を出力する。 *)
Definition eval_entry_lookup (inp : VaultSecurityInput) (dummy_len : nat) : LowObservation :=
  let len := if sec_entry_exists (input_high inp)
             then length (sec_plaintext (input_high inp))
             else dummy_len in
  mkLowObservation
    None
    (pad_to_bucket (pub_req_length (input_public inp)) len)
    (pub_header (input_public inp))
    (pub_slot_id (input_public inp)).

(** [MODEL]
    防護的エントリ照会評価関数 (eval_query)。
    エントリ存在フラグ (sec_entry_exists) を実際に評価・分岐し、
    エントリが存在する場合は平文長、非存在時はデフォルトダミー長を採用して、
    指定バケットサイズにパディングした低位観測値を出力する。 *)
Definition eval_query (inp : VaultSecurityInput) : LowObservation :=
  eval_entry_lookup inp default_dummy_len.

(** [MODEL]
    防護的Vault総合クエリ評価関数 (eval_vault_query)。
    防護的エントリ照会評価関数 (eval_query) のエイリアスとして定義し、
    重複を排除して単一の防護的照会モデルに統合する。 *)
Definition eval_vault_query (inp : VaultSecurityInput) : LowObservation :=
  eval_query inp.

(** [MODEL]
    統合セキュリティ状態遷移関数 (vault_security_step)。
    状態 s と公開入力 req を受け取り、防護的評価を経て次状態を生成する。 *)
Definition vault_security_step (s : VaultSecurityState) (req : LowPublic) : VaultSecurityState :=
  mkVaultSecurityState
    (state_high s)
    (eval_vault_query (mkVaultSecurityInput (state_high s) req)).

(** [SPEC]
    認証評価関数に対する完全非干渉性主定理 (auth_non_interference):
    低位公開入力が一致する任意の2入力に対し、ユーザー存在フラグやマスター鍵等の高位機密が
    異なっていても、評価後の低位観測値は完全に同値 (low_obs_eq) である。 *)
Theorem auth_non_interference : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  low_obs_eq (eval_auth inp1) (eval_auth inp2).
Proof.
  intros inp1 inp2 Hequiv.
  unfold eval_auth, low_obs_eq, low_input_equiv in *.
  simpl.
  destruct (sec_user_exists (input_high inp1));
    destruct (sec_user_exists (input_high inp2));
    try destruct (sec_master_key (input_high inp1));
    try destruct (sec_master_key (input_high inp2));
    rewrite Hequiv;
    repeat split; reflexivity.
Qed.

(** [SPEC]
    ユーザー存在非干渉性補題 (user_existence_non_interference):
    低位公開入力が一致する2つの入力において、ユーザー存在フラグ (sec_user_exists) が
    true と false で異なっていても、評価後の低位観測値は完全に同値 (low_obs_eq) である。 *)
Theorem user_existence_non_interference : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  sec_user_exists (input_high inp1) = true ->
  sec_user_exists (input_high inp2) = false ->
  low_obs_eq (eval_auth inp1) (eval_auth inp2).
Proof.
  intros inp1 inp2 Hequiv _ _.
  apply (auth_non_interference inp1 inp2 Hequiv).
Qed.

(** [SPEC]
    ユーザー摂動入力に対する一般化ユーザー存在非干渉性補題:
    user_perturbed 関係を満たし公開入力が等しい任意の2入力に対し、認証観測値は同値となる。 *)
Lemma user_perturbed_non_interference : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  user_perturbed (input_high inp1) (input_high inp2) ->
  low_obs_eq (eval_auth inp1) (eval_auth inp2).
Proof.
  intros inp1 inp2 Hequiv _.
  apply (auth_non_interference inp1 inp2 Hequiv).
Qed.

(** [SPEC]
    ダミー長パディング一致条件下でのエントリ照会非干渉性補題 (entry_lookup_non_interference):
    実平文長とダミー長が同一バケット境界に収まる場合、
    エントリ存在フラグが異なっていても低位観測値は完全に同値となる。 *)
Theorem entry_lookup_non_interference : forall (inp1 inp2 : VaultSecurityInput) (dummy_len : nat),
  low_input_equiv inp1 inp2 ->
  sec_entry_exists (input_high inp1) = true ->
  sec_entry_exists (input_high inp2) = false ->
  pad_to_bucket (pub_req_length (input_public inp1)) (length (sec_plaintext (input_high inp1))) =
  pad_to_bucket (pub_req_length (input_public inp1)) dummy_len ->
  low_obs_eq (eval_entry_lookup inp1 dummy_len) (eval_entry_lookup inp2 dummy_len).
Proof.
  intros inp1 inp2 dummy_len Hequiv He1 He2 Hpad.
  unfold eval_entry_lookup, low_obs_eq, low_input_equiv in *.
  simpl.
  rewrite He1, He2.
  rewrite Hequiv in *.
  rewrite Hpad.
  repeat split; reflexivity.
Qed.

(** [SPEC]
    エントリ有無非干渉性補題 (entry_existence_non_interference):
    低位公開入力が一致する2つの入力において、
    エントリ存在フラグ (sec_entry_exists) がtrue と false で異なっていても、
    平文長とダミー長が同一バケット境界にパディングされるならば、
    評価後の低位観測値は完全に同値 (low_obs_eq) である。 *)
Theorem entry_existence_non_interference : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  sec_entry_exists (input_high inp1) = true ->
  sec_entry_exists (input_high inp2) = false ->
  pad_to_bucket (pub_req_length (input_public inp1)) (length (sec_plaintext (input_high inp1))) =
  pad_to_bucket (pub_req_length (input_public inp1)) default_dummy_len ->
  low_obs_eq (eval_query inp1) (eval_query inp2).
Proof.
  intros inp1 inp2 Hequiv He1 He2 Hpad.
  unfold eval_query.
  apply entry_lookup_non_interference; assumption.
Qed.

(** [SPEC]
    エントリ摂動入力に対する一般化エントリ非干渉性補題:
    entry_perturbed 関係を満たし公開入力が等しい任意の2入力に対し、パディング長一致条件下で照会観測値は同値となる。 *)
Lemma entry_perturbed_non_interference : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  entry_perturbed (input_high inp1) (input_high inp2) ->
  pad_to_bucket (pub_req_length (input_public inp1))
    (if sec_entry_exists (input_high inp1)
     then length (sec_plaintext (input_high inp1))
     else default_dummy_len) =
  pad_to_bucket (pub_req_length (input_public inp1))
    (if sec_entry_exists (input_high inp2)
     then length (sec_plaintext (input_high inp2))
     else default_dummy_len) ->
  low_obs_eq (eval_query inp1) (eval_query inp2).
Proof.
  intros inp1 inp2 Hequiv [Hk Hu] Hpad.
  unfold eval_query, eval_entry_lookup, low_obs_eq, low_input_equiv in *.
  simpl.
  rewrite Hequiv in *.
  rewrite Hpad.
  repeat split; reflexivity.
Qed.

(** [SPEC]
    最上位セキュリティ非干渉性主定理 (vault_security_non_interference):
    低位公開入力が等しい任意の2つの入力 inp1, inp2 において、
    パディング長一致条件下では高位機密 (エントリ有無・平文データ等) が異なっていても、
    評価後の低位観測値は常に完全に同値 (low_obs_eq) である。 *)
Theorem vault_security_non_interference : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  pad_to_bucket (pub_req_length (input_public inp1))
    (if sec_entry_exists (input_high inp1)
     then length (sec_plaintext (input_high inp1))
     else default_dummy_len) =
  pad_to_bucket (pub_req_length (input_public inp1))
    (if sec_entry_exists (input_high inp2)
     then length (sec_plaintext (input_high inp2))
     else default_dummy_len) ->
  low_obs_eq (eval_vault_query inp1) (eval_vault_query inp2).
Proof.
  intros inp1 inp2 Hequiv Hpad.
  unfold eval_vault_query, eval_query, eval_entry_lookup, low_obs_eq, low_input_equiv in *.
  simpl.
  rewrite Hequiv in *.
  rewrite Hpad.
  repeat split; reflexivity.
Qed.

(** [SPEC]
    1ステップ状態遷移非干渉性主定理 (vault_step_non_interference):
    低位等価な任意の2つの状態 s1 ≈_L s2 に対し、
    同一の公開リクエスト req を与えて遷移させた後の状態も低位等価 (s1' ≈_L s2') を維持する。 *)
Theorem vault_step_non_interference : forall (s1 s2 : VaultSecurityState) (req : LowPublic),
  low_equiv s1 s2 ->
  pad_to_bucket (pub_req_length req)
    (if sec_entry_exists (state_high s1)
     then length (sec_plaintext (state_high s1))
     else default_dummy_len) =
  pad_to_bucket (pub_req_length req)
    (if sec_entry_exists (state_high s2)
     then length (sec_plaintext (state_high s2))
     else default_dummy_len) ->
  low_equiv (vault_security_step s1 req) (vault_security_step s2 req).
Proof.
  intros s1 s2 req Hequiv Hpad.
  unfold vault_security_step, low_equiv, observe_low.
  simpl.
  unfold eval_vault_query, eval_query, eval_entry_lookup, low_obs_eq.
  simpl.
  rewrite Hpad.
  repeat split; reflexivity.
Qed.

(** [SPEC]
    ユーザー列挙オラクル排除系 (no_user_enumeration_oracle):
    低位公開入力が等しい場合、観測されるエラー型はユーザー存在フラグの真偽に依存しない。 *)
Corollary no_user_enumeration_oracle : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  obs_error (eval_auth inp1) = obs_error (eval_auth inp2).
Proof.
  intros inp1 inp2 Hequiv.
  destruct (auth_non_interference inp1 inp2 Hequiv) as [Herr _].
  exact Herr.
Qed.

(** [SPEC]
    エントリ有無オラクル排除系 (no_entry_existence_oracle):
    低位公開入力が等しい場合、パディング長一致条件下で観測されるエラー型およびレスポンス長はエントリ存在フラグの真偽に依存しない。 *)
Corollary no_entry_existence_oracle : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  pad_to_bucket (pub_req_length (input_public inp1))
    (if sec_entry_exists (input_high inp1)
     then length (sec_plaintext (input_high inp1))
     else default_dummy_len) =
  pad_to_bucket (pub_req_length (input_public inp1))
    (if sec_entry_exists (input_high inp2)
     then length (sec_plaintext (input_high inp2))
     else default_dummy_len) ->
  obs_error (eval_query inp1) = obs_error (eval_query inp2) /\
  obs_length (eval_query inp1) = obs_length (eval_query inp2).
Proof.
  intros inp1 inp2 Hequiv Hpad.
  assert (Hobs := vault_security_non_interference inp1 inp2 Hequiv Hpad).
  destruct Hobs as [Herr [Hlen _]].
  split; [exact Herr | exact Hlen].
Qed.

(** [SPEC]
    レスポンス長オラクル排除系 (no_length_oracle):
    同一バケット境界にパディングされたレスポンス長は、平文の実長に依存せず完全に一致する。 *)
Corollary no_length_oracle : forall (inp1 inp2 : VaultSecurityInput),
  low_input_equiv inp1 inp2 ->
  pad_to_bucket (pub_req_length (input_public inp1))
    (if sec_entry_exists (input_high inp1)
     then length (sec_plaintext (input_high inp1))
     else default_dummy_len) =
  pad_to_bucket (pub_req_length (input_public inp1))
    (if sec_entry_exists (input_high inp2)
     then length (sec_plaintext (input_high inp2))
     else default_dummy_len) ->
  obs_length (eval_vault_query inp1) = obs_length (eval_vault_query inp2).
Proof.
  intros inp1 inp2 Hequiv Hpad.
  destruct (vault_security_non_interference inp1 inp2 Hequiv Hpad) as [_ [Hlen _]].
  exact Hlen.
Qed.
