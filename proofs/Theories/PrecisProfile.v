(** * PRECIS プロファイル正準化仕様モジュール (RFC 7564 / RFC 8265)。 *)
(** [SPEC]
    本モジュールは RFC 8265 で規定される UsernameCaseMapped プロファイルの
    大文字小文字マッピング (Case Folding) および禁止コードポイント検査を
    決定論的な純粋関数として形式定義し、その健全性および代数的特性 (冪等性) を証明する。 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.
From Fidelogic Require Import Tactics.

Local Open Scope Z_scope.

(** [MODEL]
    Unicode コードポイントの型定義。
    計算および範囲解析の容易性のため整数型 Z を用いる。 *)
Definition CodePoint : Type := Z.

(** [MODEL]
    PRECIS 文字列の型定義 (コードポイントのリスト)。 *)
Definition PrecisString : Type := list CodePoint.

(** [MODEL]
    閉区間 [low, high] にコードポイントが含まれるかを判定するブール述語。 *)
Definition in_range (low high cp : Z) : bool :=
  (low <=? cp) && (cp <=? high).

(** [SPEC]
    閉区間内コードポイントに対する範囲判定関数の真偽性補題。 *)
Lemma in_range_true : forall (low high cp : Z),
  low <= cp <= high -> in_range low high cp = true.
Proof.
  intros low high cp H.
  unfold in_range.
  apply Bool.andb_true_iff.
  split; apply Z.leb_le; lia.
Qed.

(** [SPEC]
    閉区間内コードポイントに対する範囲判定関数と同値命題の Reflection 補題。 *)
Lemma in_range_iff : forall (low high cp : Z),
  in_range low high cp = true <-> low <= cp <= high.
Proof.
  intros low high cp.
  unfold in_range.
  rewrite Bool.andb_true_iff.
  rewrite !Z.leb_le.
  lia.
Qed.

(** [SPEC]
    閉区間外コードポイントに対する範囲判定関数の偽値性補題。 *)
Lemma in_range_false : forall (low high cp : Z),
  (cp < low \/ high < cp) -> in_range low high cp = false.
Proof.
  intros low high cp H.
  unfold in_range.
  apply Bool.andb_false_iff.
  destruct H as [Hlt | Hgt]; [left | right]; apply Z.leb_gt; lia.
Qed.

(** [MODEL]
    ASCII 制御文字 (0x00..0x1F, 0x7F) の判定関数。 *)
Definition is_ascii_control (cp : CodePoint) : bool :=
  ((0 <=? cp) && (cp <=? 31)) || (cp =? 127).

(** [MODEL]
    非 ASCII 制御文字・フォーマット文字 (0x80..0x9F) の判定関数。 *)
Definition is_non_ascii_control (cp : CodePoint) : bool :=
  (128 <=? cp) && (cp <=? 159).

(** [MODEL]
    空白文字 (ASCII Space 0x20) の判定関数。 *)
Definition is_space (cp : CodePoint) : bool :=
  cp =? 32.

(** [MODEL]
    Unicode サロゲートコードポイント (0xD800..0xDFFF) の判定関数。 *)
Definition is_surrogate (cp : CodePoint) : bool :=
  (55296 <=? cp) && (cp <=? 57343).

(** [MODEL]
    私用領域 (Private Use Area - PUA) の判定関数。
    BMP (0xE000..0xF8FF), 第15面 (0xF0000..0xFFFFD), 第16面 (0x100000..0x10FFFD)。 *)
Definition is_private_use (cp : CodePoint) : bool :=
  ((57344 <=? cp) && (cp <=? 63743)) ||
  ((983040 <=? cp) && (cp <=? 1048573)) ||
  ((1048576 <=? cp) && (cp <=? 1114109)).

(** [MODEL]
    非文字 (Noncharacters) の判定関数。
    0xFDD0..0xFDEF および各面の末尾2コードポイント (mod 0x10000 が 0xFFFE または 0xFFFF)。 *)
Definition is_noncharacter (cp : CodePoint) : bool :=
  ((64976 <=? cp) && (cp <=? 65007)) ||
  ((0 <=? cp) && (cp <=? 1114111) &&
   (((cp mod 65536) =? 65534) || ((cp mod 65536) =? 65535))).

(** [MODEL]
    Unicode 有効範囲外 (cp < 0 または cp > 0x10FFFF) の判定関数。 *)
Definition is_out_of_bounds (cp : CodePoint) : bool :=
  (cp <? 0) || (1114111 <? cp).

(** [MODEL]
    総合禁止コードポイント判定関数。
    RFC 7564 Section 8.1 および RFC 8265 Section 3.2 に従い、
    制御文字、空白、サロゲート、私用領域、非文字、および範囲外文字を禁止とする。 *)
Definition is_disallowed_cp (cp : CodePoint) : bool :=
  is_out_of_bounds cp ||
  is_ascii_control cp ||
  is_non_ascii_control cp ||
  is_space cp ||
  is_surrogate cp ||
  is_private_use cp ||
  is_noncharacter cp.

(** [MODEL]
    禁止コードポイントを表す命題。 *)
Definition disallowed_cp (cp : CodePoint) : Prop :=
  is_out_of_bounds cp = true \/
  is_ascii_control cp = true \/
  is_non_ascii_control cp = true \/
  is_space cp = true \/
  is_surrogate cp = true \/
  is_private_use cp = true \/
  is_noncharacter cp = true.

(** [SPEC]
    総合禁止判定関数と禁止コードポイント命題の Reflection 補題。 *)
Lemma is_disallowed_cp_eq : forall (cp : CodePoint),
  is_disallowed_cp cp = true <-> disallowed_cp cp.
Proof.
  intros cp.
  unfold is_disallowed_cp, disallowed_cp.
  repeat rewrite Bool.orb_true_iff.
  tauto.
Qed.

(** [SPEC]
    任意のコードポイントに対する禁止判定の決定可能性補題。 *)
Lemma disallowed_cp_dec : forall (cp : CodePoint),
  {disallowed_cp cp} + {~ disallowed_cp cp}.
Proof.
  intros cp.
  destruct (is_disallowed_cp cp) eqn:H.
  - left. apply is_disallowed_cp_eq. exact H.
  - right. intro Hc. apply is_disallowed_cp_eq in Hc.
    rewrite Hc in H. discriminate H.
Qed.

(** [MODEL]
    単一コードポイントに対する Case Folding (小文字化) 写像関数。
    - ASCII 英大文字 (0x41 'A' .. 0x5A 'Z') -> cp + 32 ('a' .. 'z')
    - Latin-1 拡張大文字 (0xC0 .. 0xD6, 0xD8 .. 0xDE) -> cp + 32
    - ギリシャ文字大文字 (0x0391 .. 0x03A1, 0x03A3 .. 0x03AB) -> cp + 32
    - キリル文字大文字 (0x0410 .. 0x042F) -> cp + 32
    - その他のコードポイントは恒等写像 (不変) とする。 *)
Definition precis_fold_cp (cp : CodePoint) : CodePoint :=
  if in_range 65 90 cp then cp + 32
  else if in_range 192 214 cp then cp + 32
  else if in_range 216 222 cp then cp + 32
  else if in_range 913 929 cp then cp + 32
  else if in_range 931 939 cp then cp + 32
  else if in_range 1040 1071 cp then cp + 32
  else cp.

(** [SPEC]
    写像後コードポイントの簡約タクティック。 *)
Ltac simplify_folded cp H :=
  rewrite in_range_iff in H;
  unfold precis_fold_cp;
  repeat (
    match goal with
    | |- context [in_range ?l ?h (cp + 32)] =>
        let Hf := fresh "Hf" in
        assert (Hf : cp + 32 < l \/ h < cp + 32) by lia;
        rewrite (in_range_false l h (cp + 32) Hf); clear Hf
    end
  );
  reflexivity.

(** [SPEC]
    単一コードポイントに対する Case Folding 写像関数の不動点性 (冪等性) 補題。 *)
Lemma case_fold_idempotent : forall (cp : CodePoint),
  precis_fold_cp (precis_fold_cp cp) = precis_fold_cp cp.
Proof.
  intros cp.
  unfold precis_fold_cp.
  destruct (in_range 65 90 cp) eqn:H1.
  { simplify_folded cp H1. }
  destruct (in_range 192 214 cp) eqn:H2.
  { simplify_folded cp H2. }
  destruct (in_range 216 222 cp) eqn:H3.
  { simplify_folded cp H3. }
  destruct (in_range 913 929 cp) eqn:H4.
  { simplify_folded cp H4. }
  destruct (in_range 931 939 cp) eqn:H5.
  { simplify_folded cp H5. }
  destruct (in_range 1040 1071 cp) eqn:H6.
  { simplify_folded cp H6. }
  unfold precis_fold_cp.
  rewrite H1, H2, H3, H4, H5, H6.
  reflexivity.
Qed.

(** [SPEC]
    基本多言語面 (BMP) 低位コードポイントに対する非文字判定偽値性補題。 *)
Lemma small_noncharacter_false : forall (cp : CodePoint),
  0 <= cp <= 1103 ->
  is_noncharacter cp = false.
Proof.
  intros cp H.
  unfold is_noncharacter.
  assert (Hmod : cp mod 65536 = cp).
  { apply Z.mod_small. lia. }
  rewrite Hmod.
  destruct (64976 <=? cp) eqn:E1.
  { apply Z.leb_le in E1. lia. }
  cbn.
  destruct (cp =? 65534) eqn:E2.
  { apply Z.eqb_eq in E2. lia. }
  destruct (cp =? 65535) eqn:E3.
  { apply Z.eqb_eq in E3. lia. }
  rewrite !Bool.andb_false_r.
  reflexivity.
Qed.

(** [SPEC]
    Case Folding 写像後の小文字領域コードポイントに対する許可性 (非禁止性) 補題。 *)
Lemma folded_code_point_allowed : forall (cp : CodePoint),
  (97 <= cp <= 122 \/
   224 <= cp <= 246 \/
   248 <= cp <= 254 \/
   945 <= cp <= 961 \/
   963 <= cp <= 971 \/
   1072 <= cp <= 1103) ->
  is_disallowed_cp cp = false.
Proof.
  intros cp H.
  unfold is_disallowed_cp.
  assert (Hnonchar : is_noncharacter cp = false).
  { apply small_noncharacter_false. lia. }
  rewrite Hnonchar.
  unfold is_out_of_bounds, is_ascii_control, is_non_ascii_control, is_space,
         is_surrogate, is_private_use.
  repeat (
    match goal with
    | |- context [?l <=? cp] =>
        let E := fresh "E" in
        destruct (l <=? cp) eqn:E; [apply Z.leb_le in E; try lia |]
    | |- context [cp <=? ?h] =>
        let E := fresh "E" in
        destruct (cp <=? h) eqn:E; [apply Z.leb_le in E; try lia |]
    | |- context [cp <? ?l] =>
        let E := fresh "E" in
        destruct (cp <? l) eqn:E; [apply Z.ltb_lt in E; try lia |]
    | |- context [?h <? cp] =>
        let E := fresh "E" in
        destruct (h <? cp) eqn:E; [apply Z.ltb_lt in E; try lia |]
    | |- context [cp =? ?v] =>
        let E := fresh "E" in
        destruct (cp =? v) eqn:E; [apply Z.eqb_eq in E; try lia |]
    end
  ); reflexivity.
Qed.

(** [SPEC]
    許可コードポイントに対する Case Folding 写像の許可性保存補題。 *)
Lemma case_fold_preserves_allowed : forall (cp : CodePoint),
  is_disallowed_cp cp = false ->
  is_disallowed_cp (precis_fold_cp cp) = false.
Proof.
  intros cp H.
  unfold precis_fold_cp.
  destruct (in_range 65 90 cp) eqn:H1.
  { apply in_range_iff in H1. apply folded_code_point_allowed. lia. }
  destruct (in_range 192 214 cp) eqn:H2.
  { apply in_range_iff in H2. apply folded_code_point_allowed. lia. }
  destruct (in_range 216 222 cp) eqn:H3.
  { apply in_range_iff in H3. apply folded_code_point_allowed. lia. }
  destruct (in_range 913 929 cp) eqn:H4.
  { apply in_range_iff in H4. apply folded_code_point_allowed. lia. }
  destruct (in_range 931 939 cp) eqn:H5.
  { apply in_range_iff in H5. apply folded_code_point_allowed. lia. }
  destruct (in_range 1040 1071 cp) eqn:H6.
  { apply in_range_iff in H6. apply folded_code_point_allowed. lia. }
  exact H.
Qed.

(** [SPEC]
    許可コードポイント命題に対する Case Folding 写像の不変性補題。 *)
Lemma case_fold_preserves_allowed_prop : forall (cp : CodePoint),
  ~ disallowed_cp cp ->
  ~ disallowed_cp (precis_fold_cp cp).
Proof.
  intros cp H.
  intro Hc.
  apply H.
  apply is_disallowed_cp_eq in Hc.
  apply is_disallowed_cp_eq.
  destruct (is_disallowed_cp cp) eqn:He.
  - reflexivity.
  - apply case_fold_preserves_allowed in He.
    rewrite He in Hc. discriminate Hc.
Qed.

(** [MODEL]
    文字列全体に対する Case Folding 写像関数。 *)
Definition precis_fold_string (s : PrecisString) : PrecisString :=
  map precis_fold_cp s.

(** [SPEC]
    文字列に対する Case Folding 写像適用時の長さ不変補題。 *)
Lemma case_fold_string_length : forall (s : PrecisString),
  length (precis_fold_string s) = length s.
Proof.
  intros s. apply length_map.
Qed.

(** [SPEC]
    文字列に対する Case Folding 写像の不動点性 (冪等性) 補題。 *)
Lemma case_fold_string_idempotent : forall (s : PrecisString),
  precis_fold_string (precis_fold_string s) = precis_fold_string s.
Proof.
  intros s.
  induction s as [| c rest IH]; [reflexivity |].
  cbn. f_equal.
  - apply case_fold_idempotent.
  - exact IH.
Qed.

(** [MODEL]
    文字列中のすべてのコードポイントが許可されているかを判定するブール述語。 *)
Definition all_allowed (s : PrecisString) : bool :=
  forallb (fun cp => negb (is_disallowed_cp cp)) s.

(** [SPEC]
    文字列中の全文字許可性に対する Case Folding 写像適用後の許可性保存補題。 *)
Lemma all_allowed_folded : forall (s : PrecisString),
  all_allowed s = true ->
  all_allowed (precis_fold_string s) = true.
Proof.
  intros s.
  induction s as [| c rest IH]; [reflexivity |].
  cbn. intros H.
  apply Bool.andb_true_iff in H as [Hc Hrest].
  apply Bool.andb_true_iff.
  split.
  - apply Bool.negb_true_iff in Hc.
    apply Bool.negb_true_iff.
    apply case_fold_preserves_allowed. exact Hc.
  - apply IH. exact Hrest.
Qed.

(** [MODEL]
    UsernameCaseMapped 正準化関数 (RFC 8265 Section 3.3)。
    1. 空文字列は拒絶 (None)。
    2. 大文字小文字マッピング (Case Folding) を適用。
    3. マッピング後の文字列に対して禁止コードポイント検査を実施。
    4. 禁止文字が含まれていれば拒絶 (None)、全文字合法であれば正準化結果 (Some) を返却する。 *)
Definition precis_username_case_mapped (s : PrecisString) : option PrecisString :=
  match s with
  | [] => None
  | _ =>
      let folded := precis_fold_string s in
      if all_allowed folded then
        Some folded
      else
        None
  end.

(** [SPEC]
    正準化成功時における出力文字列の非空性保証補題。 *)
Lemma username_case_mapped_not_empty : forall (s s' : PrecisString),
  precis_username_case_mapped s = Some s' ->
  s' <> [].
Proof.
  intros s s' H.
  destruct s as [| c rest]; [discriminate H |].
  unfold precis_username_case_mapped in H.
  destruct (all_allowed (precis_fold_string (c :: rest))) eqn:He; [| discriminate H].
  injection H as Heq; subst s'.
  intro Hnil.
  unfold precis_fold_string in Hnil.
  discriminate Hnil.
Qed.

(** [SPEC]
    正準化成功時における入出力文字列の長さ保存補題。 *)
Lemma username_case_mapped_length : forall (s s' : PrecisString),
  precis_username_case_mapped s = Some s' ->
  length s' = length s.
Proof.
  intros s s' H.
  destruct s as [| c rest]; [discriminate H |].
  unfold precis_username_case_mapped in H.
  destruct (all_allowed (precis_fold_string (c :: rest))) eqn:He; [| discriminate H].
  injection H as Heq; subst s'.
  cbn. f_equal.
  apply case_fold_string_length.
Qed.

(** [SPEC]
    正準化成功時における出力文字列の全文字許可判定保証補題。 *)
Lemma username_case_mapped_all_allowed : forall (s s' : PrecisString),
  precis_username_case_mapped s = Some s' ->
  all_allowed s' = true.
Proof.
  intros s s' H.
  destruct s as [| c rest]; [discriminate H |].
  unfold precis_username_case_mapped in H.
  destruct (all_allowed (precis_fold_string (c :: rest))) eqn:He; [| discriminate H].
  injection H as Heq; subst s'.
  exact He.
Qed.

(** [SPEC]
    文字列全文字許可判定関数とリスト全要素非禁止命題の同値性補題。 *)
Lemma all_allowed_forall : forall (s : PrecisString),
  all_allowed s = true <-> Forall (fun cp => is_disallowed_cp cp = false) s.
Proof.
  intros s.
  unfold all_allowed.
  split.
  - induction s as [| c rest IH]; [constructor |].
    cbn. intros H.
    apply Bool.andb_true_iff in H as [Hc Hrest].
    apply Bool.negb_true_iff in Hc.
    constructor; [exact Hc | apply IH; exact Hrest].
  - induction s as [| c rest IH]; [reflexivity |].
    intros H. inv H.
    cbn. apply Bool.andb_true_iff.
    split; [apply Bool.negb_true_iff | apply IH]; assumption.
Qed.

(** [SPEC]
    正準化成功時における出力文字列の全文字非禁止性保証定理。 *)
Lemma username_case_mapped_no_disallowed : forall (s s' : PrecisString),
  precis_username_case_mapped s = Some s' ->
  Forall (fun cp => ~ disallowed_cp cp) s'.
Proof.
  intros s s' H.
  apply username_case_mapped_all_allowed in H.
  apply all_allowed_forall in H.
  induction H as [| x l Hx Hl IH].
  - constructor.
  - constructor.
    + intro Hc. apply is_disallowed_cp_eq in Hc.
      rewrite Hx in Hc. discriminate Hc.
    + exact IH.
Qed.

(** [SPEC]
    UsernameCaseMapped プロファイル正準化関数の冪等性主定理。
    正準化に成功した出力文字列に対し、再度正準化関数を適用しても同一の結果が得られることを保証する。 *)
Theorem username_case_mapped_idempotent : forall (s s' : PrecisString),
  precis_username_case_mapped s = Some s' ->
  precis_username_case_mapped s' = Some s'.
Proof.
  intros s s' H.
  destruct s as [| c rest]; [discriminate H |].
  unfold precis_username_case_mapped in H.
  set (folded := precis_fold_string (c :: rest)) in *.
  destruct (all_allowed folded) eqn:He; [| discriminate H].
  injection H as Heq; subst s'.
  unfold precis_username_case_mapped.
  destruct folded as [| c' rest'] eqn:Hfolded.
  - unfold folded, precis_fold_string in Hfolded. discriminate Hfolded.
  - assert (Hfold_id : precis_fold_string (c' :: rest') = c' :: rest').
    { rewrite <- Hfolded.
      subst folded.
      apply case_fold_string_idempotent. }
    rewrite Hfold_id.
    rewrite He.
    reflexivity.
Qed.

(** [SPEC]
    大文字小文字の差異しかない2つの入力文字列に対する正準化結果の一致性 (大文字小文字不変性) 主定理。 *)
Theorem username_case_mapped_case_insensitive : forall (s1 s2 : PrecisString),
  precis_fold_string s1 = precis_fold_string s2 ->
  precis_username_case_mapped s1 = precis_username_case_mapped s2.
Proof.
  intros s1 s2 H.
  destruct s1 as [| c1 r1]; destruct s2 as [| c2 r2].
  - reflexivity.
  - unfold precis_fold_string in H. cbn in H. discriminate H.
  - unfold precis_fold_string in H. cbn in H. discriminate H.
  - unfold precis_username_case_mapped.
    rewrite H.
    reflexivity.
Qed.

(******************************************************************************)
(* OpaqueString プロファイル仕様 (RFC 7564 / RFC 8265 Section 4)              *)
(******************************************************************************)

(** [MODEL]
    FreeformClass 用の禁止コードポイント判定関数 (RFC 7564 Section 4.3 / RFC 8265 Section 4.2)。
    OpaqueString プロファイルでは空白文字 (0x20) を許可するため、
    is_space を除外し、制御文字、サロゲート、私用領域、非文字、範囲外文字のみを禁止とする。 *)
Definition is_opaque_disallowed_cp (cp : CodePoint) : bool :=
  is_out_of_bounds cp ||
  is_ascii_control cp ||
  is_non_ascii_control cp ||
  is_surrogate cp ||
  is_private_use cp ||
  is_noncharacter cp.

(** [MODEL]
    FreeformClass 用の禁止コードポイントを表す命題。 *)
Definition opaque_disallowed_cp (cp : CodePoint) : Prop :=
  is_out_of_bounds cp = true \/
  is_ascii_control cp = true \/
  is_non_ascii_control cp = true \/
  is_surrogate cp = true \/
  is_private_use cp = true \/
  is_noncharacter cp = true.

(** [SPEC]
    FreeformClass 禁止判定関数と禁止コードポイント命題の Reflection 補題。 *)
Lemma is_opaque_disallowed_cp_eq : forall (cp : CodePoint),
  is_opaque_disallowed_cp cp = true <-> opaque_disallowed_cp cp.
Proof.
  intros cp.
  unfold is_opaque_disallowed_cp, opaque_disallowed_cp.
  repeat rewrite Bool.orb_true_iff.
  tauto.
Qed.

(** [SPEC]
    FreeformClass 禁止判定の決定可能性補題。 *)
Lemma opaque_disallowed_cp_dec : forall (cp : CodePoint),
  {opaque_disallowed_cp cp} + {~ opaque_disallowed_cp cp}.
Proof.
  intros cp.
  destruct (is_opaque_disallowed_cp cp) eqn:H.
  - left. apply is_opaque_disallowed_cp_eq. exact H.
  - right. intro Hc. apply is_opaque_disallowed_cp_eq in Hc.
    rewrite Hc in H. discriminate H.
Qed.

(** [SPEC]
    空白文字 (ASCII Space 0x20) に対する FreeformClass での許可性補題。 *)
Lemma space_opaque_allowed :
  is_opaque_disallowed_cp 32 = false.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    FreeformClass の禁止文字は IdentifierClass でも禁止される包含関係補題。 *)
Lemma opaque_disallowed_implies_disallowed : forall (cp : CodePoint),
  is_opaque_disallowed_cp cp = true ->
  is_disallowed_cp cp = true.
Proof.
  intros cp H.
  unfold is_disallowed_cp, is_opaque_disallowed_cp in *.
  repeat rewrite Bool.orb_true_iff in *.
  tauto.
Qed.

(** [MODEL]
    ハングル音節合成 (Jamo L + V -> Syllable) の算術計算関数 (Unicode Standard 3.12)。
    LBase = 0x1100 (4352), VBase = 0x1161 (4449), SBase = 0xAC00 (44032)。
    S = SBase + (L - LBase) * 588 + (V - VBase) * 28。 *)
Definition compose_hangul_syllable (l v : CodePoint) : CodePoint :=
  44032 + (l - 4352) * 588 + (v - 4449) * 28.

(** [SPEC]
    ハングル音節合成結果の値域保証補題。
    正当な Jamo L (0x1100..0x1112) および V (0x1161..0x1175) に対し、
    合成結果は BMP 内のハングル音節領域 (44032..55176) に厳密に収まることを示す。 *)
Lemma compose_hangul_syllable_range : forall (l v : CodePoint),
  4352 <= l <= 4370 ->
  4449 <= v <= 4469 ->
  44032 <= compose_hangul_syllable l v <= 55176.
Proof.
  intros l v Hl Hv.
  unfold compose_hangul_syllable.
  assert (Hl_range : 0 <= l - 4352 <= 18) by lia.
  assert (Hv_range : 0 <= v - 4449 <= 20) by lia.
  destruct Hl_range as [Hl_low Hl_high].
  destruct Hv_range as [Hv_low Hv_high].
  assert (H1 : 0 <= (l - 4352) * 588 <= 18 * 588).
  { split.
    - apply Z.mul_nonneg_nonneg; lia.
    - apply Z.mul_le_mono_nonneg_r; lia. }
  assert (H2 : 0 <= (v - 4449) * 28 <= 20 * 28).
  { split.
    - apply Z.mul_nonneg_nonneg; lia.
    - apply Z.mul_le_mono_nonneg_r; lia. }
  destruct H1 as [H1_low H1_high].
  destruct H2 as [H2_low H2_high].
  split.
  - lia.
  - assert (Hsum : (l - 4352) * 588 + (v - 4449) * 28 <= 18 * 588 + 20 * 28) by lia.
    change (18 * 588 + 20 * 28) with 11144 in Hsum.
    lia.
Qed.

(** [MODEL]
    単一ペアに対する Unicode 正準合成 (Canonical Composition) 写像関数。
    基底文字 (Base) と結合文字 (Combining Mark) のペアを合成文字へと縮約する。
    - Latin 基底文字 ('A', 'C', 'E', 'I', 'O', 'U', 'a', 'c', 'e', 'i', 'o', 'u') と
      ダイアクリティカルマーク (Grave, Acute, Circumflex, Tilde, Diaeresis, Ring above, Cedilla) の合成。
    - ハングル Jamo (L, V) の音節合成 (0x1100..0x1112 + 0x1161..0x1175 -> 0xAC00..0xD7A3)。
    - 合成不可能なペアに対しては None を返却する。 *)
Definition compose_pair (c1 c2 : CodePoint) : option CodePoint :=
  (* Latin 'A' (65) *)
  if c1 =? 65 then
    if c2 =? 768 then Some 192
    else if c2 =? 769 then Some 193
    else if c2 =? 770 then Some 194
    else if c2 =? 771 then Some 195
    else if c2 =? 776 then Some 196
    else if c2 =? 778 then Some 197
    else None
  (* Latin 'C' (67) *)
  else if c1 =? 67 then
    if c2 =? 807 then Some 199
    else None
  (* Latin 'E' (69) *)
  else if c1 =? 69 then
    if c2 =? 768 then Some 200
    else if c2 =? 769 then Some 201
    else if c2 =? 770 then Some 202
    else if c2 =? 776 then Some 203
    else None
  (* Latin 'I' (73) *)
  else if c1 =? 73 then
    if c2 =? 768 then Some 204
    else if c2 =? 769 then Some 205
    else if c2 =? 770 then Some 206
    else if c2 =? 776 then Some 207
    else None
  (* Latin 'O' (79) *)
  else if c1 =? 79 then
    if c2 =? 768 then Some 210
    else if c2 =? 769 then Some 211
    else if c2 =? 770 then Some 212
    else if c2 =? 771 then Some 213
    else if c2 =? 776 then Some 214
    else None
  (* Latin 'U' (85) *)
  else if c1 =? 85 then
    if c2 =? 768 then Some 217
    else if c2 =? 769 then Some 218
    else if c2 =? 770 then Some 219
    else if c2 =? 776 then Some 220
    else None
  (* Latin 'a' (97) *)
  else if c1 =? 97 then
    if c2 =? 768 then Some 224
    else if c2 =? 769 then Some 225
    else if c2 =? 770 then Some 226
    else if c2 =? 771 then Some 227
    else if c2 =? 776 then Some 228
    else if c2 =? 778 then Some 229
    else None
  (* Latin 'c' (99) *)
  else if c1 =? 99 then
    if c2 =? 807 then Some 231
    else None
  (* Latin 'e' (101) *)
  else if c1 =? 101 then
    if c2 =? 768 then Some 232
    else if c2 =? 769 then Some 233
    else if c2 =? 770 then Some 234
    else if c2 =? 776 then Some 235
    else None
  (* Latin 'i' (105) *)
  else if c1 =? 105 then
    if c2 =? 768 then Some 236
    else if c2 =? 769 then Some 237
    else if c2 =? 770 then Some 238
    else if c2 =? 776 then Some 239
    else None
  (* Latin 'o' (111) *)
  else if c1 =? 111 then
    if c2 =? 768 then Some 242
    else if c2 =? 769 then Some 243
    else if c2 =? 770 then Some 244
    else if c2 =? 771 then Some 245
    else if c2 =? 776 then Some 246
    else None
  (* Latin 'u' (117) *)
  else if c1 =? 117 then
    if c2 =? 768 then Some 249
    else if c2 =? 769 then Some 250
    else if c2 =? 770 then Some 251
    else if c2 =? 776 then Some 252
    else None
  (* Hangul L + V *)
  else if (4352 <=? c1) && (c1 <=? 4370) && (4449 <=? c2) && (c2 <=? 4469) then
    Some (compose_hangul_syllable c1 c2)
  else
    None.

(** [SPEC]
    合成後コードポイントの出力値域補題。
    正準合成の結果は、Latin 合成文字領域 (192..252) または
    ハングル音節領域 (44032..55176) のいずれかに属することを示す。 *)
Lemma compose_pair_range : forall (c1 c2 c' : CodePoint),
  compose_pair c1 c2 = Some c' ->
  (192 <= c' <= 252 \/ 44032 <= c' <= 55176).
Proof.
  intros c1 c2 c' H.
  unfold compose_pair in H.
  repeat match goal with
  | H : context [ if ?b then _ else _ ] |- _ =>
      let E := fresh "E" in
      destruct b eqn:E; [ try (injection H as Heq; subst c'; left; lia) | try discriminate H ]
  end.
  match goal with
  | E : (_ && _)%bool = true |- _ =>
      repeat rewrite Bool.andb_true_iff in E;
      destruct E as [[[Hl1 Hl2] Hv1] Hv2];
      apply Z.leb_le in Hl1; apply Z.leb_le in Hl2;
      apply Z.leb_le in Hv1; apply Z.leb_le in Hv2
  end.
  injection H as Heq; subst c'.
  right.
  apply compose_hangul_syllable_range; lia.
Qed.

(** [SPEC]
    合成後コードポイントの終端性補題 (左側オペランドとしての不活性性)。
    compose_pair で生成された合成文字は、更なる合成規則の左オペランドになり得ないことを示す。 *)
Lemma compose_pair_terminal_left : forall (c1 c2 c' : CodePoint),
  compose_pair c1 c2 = Some c' ->
  forall (x : CodePoint), compose_pair c' x = None.
Proof.
  intros c1 c2 c' Hcomp x.
  apply compose_pair_range in Hcomp as [Hlat | Hkor].
  - unfold compose_pair.
    repeat (
      match goal with
      | |- context [c' =? ?v] =>
          let E := fresh "E" in
          destruct (c' =? v) eqn:E; [apply Z.eqb_eq in E; lia | clear E]
      end
    ).
    destruct (4352 <=? c') eqn:E; [apply Z.leb_le in E; lia | reflexivity].
  - unfold compose_pair.
    repeat (
      match goal with
      | |- context [c' =? ?v] =>
          let E := fresh "E" in
          destruct (c' =? v) eqn:E; [apply Z.eqb_eq in E; lia | clear E]
      end
    ).
    destruct (4352 <=? c') eqn:E4352; [ | reflexivity ].
    destruct (c' <=? 4370) eqn:E4370; [ apply Z.leb_le in E4370; lia | reflexivity ].
Qed.

(** [SPEC]
    合成後コードポイントの終端性補題 (右側オペランドとしての不活性性)。
    compose_pair で生成された合成文字は、更なる合成規則の右オペランド (結合文字) になり得ないことを示す。 *)
Lemma compose_pair_terminal_right : forall (c1 c2 c' : CodePoint),
  compose_pair c1 c2 = Some c' ->
  forall (x : CodePoint), compose_pair x c' = None.
Proof.
  intros c1 c2 c' Hcomp x.
  apply compose_pair_range in Hcomp as [Hlat | Hkor].
  - unfold compose_pair.
    repeat (
      match goal with
      | |- context [c' =? ?v] =>
          let E := fresh "E" in
          destruct (c' =? v) eqn:E; [apply Z.eqb_eq in E; lia | clear E]
      end
    ).
    destruct (x =? 65); [ reflexivity | ].
    destruct (x =? 67); [ reflexivity | ].
    destruct (x =? 69); [ reflexivity | ].
    destruct (x =? 73); [ reflexivity | ].
    destruct (x =? 79); [ reflexivity | ].
    destruct (x =? 85); [ reflexivity | ].
    destruct (x =? 97); [ reflexivity | ].
    destruct (x =? 99); [ reflexivity | ].
    destruct (x =? 101); [ reflexivity | ].
    destruct (x =? 105); [ reflexivity | ].
    destruct (x =? 111); [ reflexivity | ].
    destruct (x =? 117); [ reflexivity | ].
    destruct (4352 <=? x); [ | reflexivity ].
    destruct (x <=? 4370); [ | reflexivity ].
    destruct (4449 <=? c') eqn:E; [apply Z.leb_le in E; lia | reflexivity].
  - unfold compose_pair.
    repeat (
      match goal with
      | |- context [c' =? ?v] =>
          let E := fresh "E" in
          destruct (c' =? v) eqn:E; [apply Z.eqb_eq in E; lia | clear E]
      end
    ).
    destruct (x =? 65); [ reflexivity | ].
    destruct (x =? 67); [ reflexivity | ].
    destruct (x =? 69); [ reflexivity | ].
    destruct (x =? 73); [ reflexivity | ].
    destruct (x =? 79); [ reflexivity | ].
    destruct (x =? 85); [ reflexivity | ].
    destruct (x =? 97); [ reflexivity | ].
    destruct (x =? 99); [ reflexivity | ].
    destruct (x =? 101); [ reflexivity | ].
    destruct (x =? 105); [ reflexivity | ].
    destruct (x =? 111); [ reflexivity | ].
    destruct (x =? 117); [ reflexivity | ].
    destruct (4352 <=? x); [ | reflexivity ].
    destruct (x <=? 4370); [ | reflexivity ].
    destruct (4449 <=? c'); [ | reflexivity ].
    destruct (c' <=? 4469) eqn:E; [apply Z.leb_le in E; lia | reflexivity].
Qed.

(** [SPEC]
    合成後コードポイントに対する FreeformClass 許可性保証補題。
    正準合成によって生成されたコードポイントは、一切の禁止領域 (制御文字、サロゲート、私用領域、非文字) に含まれないことを示す。 *)
Lemma composed_code_point_opaque_allowed : forall (c1 c2 c' : CodePoint),
  compose_pair c1 c2 = Some c' ->
  is_opaque_disallowed_cp c' = false.
Proof.
  intros c1 c2 c' Hcomp.
  apply compose_pair_range in Hcomp as [Hlatin | Hhangul].
  - unfold is_opaque_disallowed_cp.
    assert (Hnonchar : is_noncharacter c' = false).
    { apply small_noncharacter_false. lia. }
    rewrite Hnonchar.
    unfold is_out_of_bounds, is_ascii_control, is_non_ascii_control,
           is_surrogate, is_private_use.
    repeat (
      match goal with
      | |- context [?l <=? c'] =>
          let E := fresh "E" in
          destruct (l <=? c') eqn:E; [apply Z.leb_le in E; try lia |]
      | |- context [c' <=? ?h] =>
          let E := fresh "E" in
          destruct (c' <=? h) eqn:E; [apply Z.leb_le in E; try lia |]
      | |- context [c' <? ?l] =>
          let E := fresh "E" in
          destruct (c' <? l) eqn:E; [apply Z.ltb_lt in E; try lia |]
      | |- context [?h <? c'] =>
          let E := fresh "E" in
          destruct (h <? c') eqn:E; [apply Z.ltb_lt in E; try lia |]
      | |- context [c' =? ?v] =>
          let E := fresh "E" in
          destruct (c' =? v) eqn:E; [apply Z.eqb_eq in E; try lia |]
      end
    ); reflexivity.
  - unfold is_opaque_disallowed_cp.
    assert (Hnonchar : is_noncharacter c' = false).
    { unfold is_noncharacter.
      assert (Hmod : c' mod 65536 = c').
      { apply Z.mod_small. lia. }
      rewrite Hmod.
      destruct (64976 <=? c') eqn:E1.
      { apply Z.leb_le in E1. lia. }
      cbn.
      destruct (c' =? 65534) eqn:E2.
      { apply Z.eqb_eq in E2. lia. }
      destruct (c' =? 65535) eqn:E3.
      { apply Z.eqb_eq in E3. lia. }
      rewrite !Bool.andb_false_r.
      reflexivity. }
    rewrite Hnonchar.
    unfold is_opaque_disallowed_cp, is_out_of_bounds, is_ascii_control,
           is_non_ascii_control, is_surrogate, is_private_use.
    repeat (
      match goal with
      | |- context [?l <=? c'] =>
          let E := fresh "E" in
          destruct (l <=? c') eqn:E; [apply Z.leb_le in E; try lia |]
      | |- context [c' <=? ?h] =>
          let E := fresh "E" in
          destruct (c' <=? h) eqn:E; [apply Z.leb_le in E; try lia |]
      | |- context [c' <? ?l] =>
          let E := fresh "E" in
          destruct (c' <? l) eqn:E; [apply Z.ltb_lt in E; try lia |]
      | |- context [?h <? c'] =>
          let E := fresh "E" in
          destruct (h <? c') eqn:E; [apply Z.ltb_lt in E; try lia |]
      | |- context [c' =? ?v] =>
          let E := fresh "E" in
          destruct (c' =? v) eqn:E; [apply Z.eqb_eq in E; try lia |]
      end
    ); reflexivity.
Qed.

(** [MODEL]
    Unicode 正規化形式 NFC (Normalization Form C) を適用する純粋関数。
    リストを走査し、隣接する正準合成可能ペアを決定論的に縮約する。 *)
Fixpoint precis_nfc_normalize (s : PrecisString) : PrecisString :=
  match s with
  | [] => []
  | c1 :: rest1 =>
      match rest1 with
      | [] => [c1]
      | c2 :: rest2 =>
          match compose_pair c1 c2 with
          | Some c' => c' :: precis_nfc_normalize rest2
          | None => c1 :: precis_nfc_normalize rest1
          end
      end
  end.

(** [MODEL]
    文字列中のすべてのコードポイントが FreeformClass で許可されているかを判定するブール述語。 *)
Definition all_opaque_allowed (s : PrecisString) : bool :=
  forallb (fun cp => negb (is_opaque_disallowed_cp cp)) s.

(** [SPEC]
    全文字許可文字列に対する NFC 正規化適用後の許可性保存補題。 *)
Lemma all_opaque_allowed_nfc : forall (s : PrecisString),
  all_opaque_allowed s = true ->
  all_opaque_allowed (precis_nfc_normalize s) = true.
Proof.
  unfold all_opaque_allowed.
  assert (Hlen : forall (n : nat) (s : PrecisString),
    (length s <= n)%nat ->
    forallb (fun cp => negb (is_opaque_disallowed_cp cp)) s = true ->
    forallb (fun cp => negb (is_opaque_disallowed_cp cp)) (precis_nfc_normalize s) = true).
  { induction n as [| n' IH].
    - intros s Hlen_s Hallow.
      destruct s as [| c rest]; [reflexivity |].
      cbn in Hlen_s. lia.
    - intros s Hlen_s Hallow.
      destruct s as [| c1 [| c2 rest2]].
      + reflexivity.
      + cbn in Hallow |- *. exact Hallow.
      + cbn in Hallow.
        repeat rewrite Bool.andb_true_iff in Hallow.
        destruct Hallow as [Hc1 [Hc2 Hrest2]].
        cbn [precis_nfc_normalize].
        destruct (compose_pair c1 c2) as [c' |] eqn:Hcomp.
        * cbn.
          apply Bool.andb_true_iff.
          split.
          { apply Bool.negb_true_iff.
            apply (composed_code_point_opaque_allowed c1 c2 c' Hcomp). }
          { apply (IH rest2).
            - cbn in Hlen_s. lia.
            - exact Hrest2. }
        * cbn.
          apply Bool.andb_true_iff.
          split.
          { exact Hc1. }
          { apply (IH (c2 :: rest2)).
            - cbn in Hlen_s |- *. lia.
            - cbn.
              apply Bool.andb_true_iff.
              split; [ exact Hc2 | exact Hrest2 ]. } }
  intros s Hallow.
  apply (Hlen (length s) s); [lia | exact Hallow].
Qed.

(** [MODEL]
    文字列中の隣接文字に未合成ペアが存在しないことを表す命題。 *)
Fixpoint nfc_no_compose (s : PrecisString) : Prop :=
  match s with
  | [] => True
  | [_] => True
  | c1 :: ((c2 :: _) as rest) =>
      compose_pair c1 c2 = None /\ nfc_no_compose rest
  end.

(** [SPEC]
    未合成ペア非存在文字列に対する NFC 正規化の恒等性補題。 *)
Lemma nfc_no_compose_id : forall (s : PrecisString),
  nfc_no_compose s ->
  precis_nfc_normalize s = s.
Proof.
  induction s as [| c1 [| c2 rest] IH]; [reflexivity | reflexivity |].
  cbn. intros [Hnone Hrest].
  rewrite Hnone.
  f_equal.
  apply IH.
  exact Hrest.
Qed.

(** [SPEC]
    2要素以上の先頭に対する NFC 正規化の展開等式補題。 *)
Lemma precis_nfc_normalize_cons_cons : forall (c1 c2 : CodePoint) (rest : PrecisString),
  precis_nfc_normalize (c1 :: c2 :: rest) =
  match compose_pair c1 c2 with
  | Some c' => c' :: precis_nfc_normalize rest
  | None => c1 :: precis_nfc_normalize (c2 :: rest)
  end.
Proof.
  intros. reflexivity.
Qed.

(** [SPEC]
    非空文字列に対する NFC 正規化結果の先頭要素存在補題。 *)
Lemma precis_nfc_normalize_cons : forall (c : CodePoint) (rest : PrecisString),
  exists (h : CodePoint) (t : PrecisString),
    precis_nfc_normalize (c :: rest) = h :: t.
Proof.
  intros c rest.
  destruct rest as [| c2 rest2].
  - exists c, []. reflexivity.
  - rewrite precis_nfc_normalize_cons_cons.
    destruct (compose_pair c c2) as [c' |] eqn:E.
    + exists c', (precis_nfc_normalize rest2). reflexivity.
    + exists c, (precis_nfc_normalize (c2 :: rest2)). reflexivity.
Qed.

(** [SPEC]
    非空文字列に対する NFC 正規化結果の先頭要素特徴づけ補題。 *)
Lemma nfc_hd_cases : forall (c : CodePoint) (rest : PrecisString),
  hd c (precis_nfc_normalize (c :: rest)) = c \/
  (exists (c2 : CodePoint) (rest2 : PrecisString) (c' : CodePoint),
     rest = c2 :: rest2 /\
     compose_pair c c2 = Some c' /\
     hd c (precis_nfc_normalize (c :: rest)) = c').
Proof.
  intros c rest.
  destruct rest as [| c2 rest2].
  - left. reflexivity.
  - rewrite precis_nfc_normalize_cons_cons.
    destruct (compose_pair c c2) as [c' |] eqn:E.
    + right. exists c2, rest2, c'.
      split; [reflexivity | split; [exact E | reflexivity]].
    + left. reflexivity.
Qed.

(** [SPEC]
    NFC 正規化結果に対する未合成ペア非存在性 (不動点条件充足) 補題。 *)
Lemma precis_nfc_normalize_no_compose : forall (s : PrecisString),
  nfc_no_compose (precis_nfc_normalize s).
Proof.
  assert (Hlen : forall (n : nat) (s : PrecisString),
    (length s <= n)%nat ->
    nfc_no_compose (precis_nfc_normalize s)).
  { induction n as [| n' IH].
    - intros s Hlen_s.
      destruct s as [| c rest]; [cbn; exact I |].
      cbn in Hlen_s. lia.
    - intros s Hlen_s.
      destruct s as [| c1 [| c2 rest2]].
      + cbn. exact I.
      + cbn. exact I.
      + rewrite precis_nfc_normalize_cons_cons.
        destruct (compose_pair c1 c2) as [c' |] eqn:Hcomp.
        * assert (Hlen2 : (length rest2 <= n')%nat) by (cbn in Hlen_s; lia).
          specialize (IH rest2 Hlen2).
          destruct (precis_nfc_normalize rest2) as [| h2 t2] eqn:Hnorm2.
          { cbn. exact I. }
          { cbn. split.
            - apply (compose_pair_terminal_left c1 c2 c' Hcomp h2).
            - exact IH. }
        * assert (Hlen1 : (length (c2 :: rest2) <= n')%nat) by (cbn in Hlen_s |- *; lia).
          specialize (IH (c2 :: rest2) Hlen1).
          destruct (precis_nfc_normalize_cons c2 rest2) as [h1 [t1 Hnorm1]].
          rewrite Hnorm1 in IH |- *.
          cbn. split.
          { assert (Hhd : h1 = hd c2 (precis_nfc_normalize (c2 :: rest2)))
               by (rewrite Hnorm1; reflexivity).
            destruct (nfc_hd_cases c2 rest2) as [Hcase | [c3 [rest3 [c23 [Hrest2 [Hcomp23 Hcase]]]]]].
            - rewrite Hcase in Hhd. subst h1. exact Hcomp.
            - rewrite Hcase in Hhd. subst h1.
              apply (compose_pair_terminal_right c2 c3 c23 Hcomp23 c1). }
          { exact IH. } }
  intros s.
  apply (Hlen (length s) s).
  lia.
Qed.

(** [SPEC]
    Unicode 正規化形式 NFC の不動点性 (冪等性) 主定理。
    任意の文字列に対し、NFC 正規化を再帰的に適用しても結果が不変であることを数学的に保証する。 *)
Theorem nfc_normalize_idempotent : forall (s : PrecisString),
  precis_nfc_normalize (precis_nfc_normalize s) = precis_nfc_normalize s.
Proof.
  intros s.
  apply nfc_no_compose_id.
  apply precis_nfc_normalize_no_compose.
Qed.

(** [MODEL]
    OpaqueString 正準化関数 (RFC 8265 Section 4.2)。
    1. 空文字列は拒絶 (None)。
    2. 大文字小文字マッピングは適用せず、Unicode 正規化形式 NFC のみを適用。
    3. 正規化後の文字列に対して FreeformClass 禁止コードポイント検査を実施。
    4. 禁止文字が含まれていれば拒絶 (None)、全文字合法であれば正準化結果 (Some) を返却する。 *)
Definition precis_opaque_string (s : PrecisString) : option PrecisString :=
  match s with
  | [] => None
  | _ =>
      let normalized := precis_nfc_normalize s in
      if all_opaque_allowed normalized then
        Some normalized
      else
        None
  end.

(** [SPEC]
    正準化成功時における出力文字列の非空性保証補題。 *)
Lemma opaque_string_not_empty : forall (s s' : PrecisString),
  precis_opaque_string s = Some s' ->
  s' <> [].
Proof.
  intros s s' H.
  destruct s as [| c rest]; [ discriminate H | ].
  unfold precis_opaque_string in H. cbv zeta in H.
  destruct (all_opaque_allowed (precis_nfc_normalize (c :: rest))) eqn:He; [ | discriminate H ].
  injection H as Heq; subst s'.
  intro Hnil.
  destruct rest as [| c2 rest2]; [ discriminate Hnil | ].
  destruct (compose_pair c c2); discriminate Hnil.
Qed.

(** [SPEC]
    正準化成功時における出力文字列の全文字許可判定保証補題。 *)
Lemma opaque_string_all_allowed : forall (s s' : PrecisString),
  precis_opaque_string s = Some s' ->
  all_opaque_allowed s' = true.
Proof.
  intros s s' H.
  destruct s as [| c rest]; [ discriminate H | ].
  unfold precis_opaque_string in H. cbv zeta in H.
  destruct (all_opaque_allowed (precis_nfc_normalize (c :: rest))) eqn:He; [ | discriminate H ].
  injection H as Heq; subst s'.
  exact He.
Qed.

(** [SPEC]
    FreeformClass 文字列全文字許可判定関数とリスト全要素非禁止命題の同値性補題。 *)
Lemma all_opaque_allowed_forall : forall (s : PrecisString),
  all_opaque_allowed s = true <-> Forall (fun cp => is_opaque_disallowed_cp cp = false) s.
Proof.
  intros s.
  unfold all_opaque_allowed.
  split.
  - induction s as [| c rest IH]; [constructor |].
    cbn. intros H.
    apply Bool.andb_true_iff in H as [Hc Hrest].
    apply Bool.negb_true_iff in Hc.
    constructor; [exact Hc | apply IH; exact Hrest].
  - induction s as [| c rest IH]; [reflexivity |].
    intros H. inv H.
    cbn. apply Bool.andb_true_iff.
    split; [apply Bool.negb_true_iff | apply IH]; assumption.
Qed.

(** [SPEC]
    正準化成功時における出力文字列の全文字非禁止性保証定理。 *)
Theorem opaque_string_no_disallowed : forall (s s' : PrecisString),
  precis_opaque_string s = Some s' ->
  Forall (fun cp => ~ opaque_disallowed_cp cp) s'.
Proof.
  intros s s' H.
  apply opaque_string_all_allowed in H.
  apply all_opaque_allowed_forall in H.
  induction H as [| x l Hx Hl IH].
  - constructor.
  - constructor.
    + intro Hc. apply is_opaque_disallowed_cp_eq in Hc.
      rewrite Hx in Hc. discriminate Hc.
    + exact IH.
Qed.

(** [SPEC]
    OpaqueString プロファイル正準化関数の冪等性主定理。
    正準化に成功した任意の出力文字列に対し、再度正準化関数を適用しても同一の結果が得られることを保証する。 *)
Theorem opaque_string_idempotent : forall (s s' : PrecisString),
  precis_opaque_string s = Some s' ->
  precis_opaque_string s' = Some s'.
Proof.
  intros s s' H.
  destruct s as [| c rest]; [ discriminate H | ].
  unfold precis_opaque_string in H. cbv zeta in H.
  set (norm := precis_nfc_normalize (c :: rest)) in *.
  destruct (all_opaque_allowed norm) eqn:He; [ | discriminate H ].
  injection H as Heq; subst s'.
  unfold precis_opaque_string.
  destruct norm as [| c' rest'] eqn:Hnorm.
  - destruct (precis_nfc_normalize_cons c rest) as [h [t Hcons]].
    unfold norm in Hnorm.
    rewrite Hcons in Hnorm. discriminate Hnorm.
  - assert (Hnorm_id : precis_nfc_normalize (c' :: rest') = c' :: rest').
    { rewrite <- Hnorm.
      subst norm.
      apply nfc_normalize_idempotent. }
    rewrite Hnorm_id.
    rewrite He.
    reflexivity.
Qed.

(** [SPEC]
    テストベクタ検証補題: 空白文字を含むパスワードが OpaqueString で拒絶されず正準化されることの検証。 *)
Lemma opaque_string_password_with_space :
  precis_opaque_string [112; 97; 115; 115; 32; 119; 111; 114; 100] =
  Some [112; 97; 115; 115; 32; 119; 111; 114; 100].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    テストベクタ検証補題: 'e' (101) + 結合鋭アクセント (769) が合成文字 'é' (233) に正準化されることの検証。 *)
Lemma opaque_string_nfd_acute :
  precis_opaque_string [101; 769] = Some [233].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    テストベクタ検証補題: ハングル Jamo L (4352) + V (4449) が合成音節 '가' (44032) に正準化されることの検証。 *)
Lemma opaque_string_hangul_ga :
  precis_opaque_string [4352; 4449] = Some [44032].
Proof.
  reflexivity.
Qed.

(** PRECIS 既知テストベクタ決定性補題群 (RFC 7564 / RFC 8265)。 *)

Section PrecisTestVectors.

(** [SPEC]
    UsernameCaseMapped テストベクタ: ASCII 英大文字小文字混在文字列 ("User") の小文字化検証。 *)
Lemma test_vector_username_fold_ascii_mixed :
  precis_username_case_mapped [85; 115; 101; 114] = Some [117; 115; 101; 114].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: ASCII 全英大文字 ("USER") の小文字化検証。 *)
Lemma test_vector_username_fold_ascii_upper :
  precis_username_case_mapped [85; 83; 69; 82] = Some [117; 115; 101; 114].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: ASCII 小文字文字列 ("user") の恒等写像検証。 *)
Lemma test_vector_username_fold_ascii_lower :
  precis_username_case_mapped [117; 115; 101; 114] = Some [117; 115; 101; 114].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: ギリシャ文字大文字 ("ΟΣ") の小文字化 ("οσ") 検証。 *)
Lemma test_vector_username_fold_greek :
  precis_username_case_mapped [927; 931] = Some [959; 963].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: キリル文字大文字 ("Иван") の小文字化 ("иван") 検証。 *)
Lemma test_vector_username_fold_cyrillic :
  precis_username_case_mapped [1048; 1074; 1072; 1085] = Some [1080; 1074; 1072; 1085].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: Latin-1 補助大文字 ("É") の小文字化 ("é") 検証。 *)
Lemma test_vector_username_fold_latin_accent :
  precis_username_case_mapped [201] = Some [233].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: 空文字列拒絶 (None) の検証。 *)
Lemma test_vector_username_reject_empty :
  precis_username_case_mapped [] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: 空白文字混入文字列 ("user name") の拒絶 (None) 検証。 *)
Lemma test_vector_username_reject_space :
  precis_username_case_mapped [117; 115; 101; 114; 32; 110; 97; 109; 101] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: ASCII NUL 制御文字混入の拒絶 (None) 検証。 *)
Lemma test_vector_username_reject_nul :
  precis_username_case_mapped [0] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: 水平タブ制御文字混入の拒絶 (None) 検証。 *)
Lemma test_vector_username_reject_tab :
  precis_username_case_mapped [117; 9; 115] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: Unicode サロゲートコードポイント (0xD800) の拒絶 (None) 検証。 *)
Lemma test_vector_username_reject_surrogate :
  precis_username_case_mapped [55296] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: 私用領域コードポイント (0xE000) の拒絶 (None) 検証。 *)
Lemma test_vector_username_reject_pua :
  precis_username_case_mapped [57344] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: 非文字 (0xFFFF) の拒絶 (None) 検証。 *)
Lemma test_vector_username_reject_nonchar_ffff :
  precis_username_case_mapped [65535] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped テストベクタ: 非文字 (0xFDD0) の拒絶 (None) 検証。 *)
Lemma test_vector_username_reject_nonchar_fdd0 :
  precis_username_case_mapped [64976] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: 英大文字小文字混在パスワード ("PassWord") の大文字保持検証。 *)
Lemma test_vector_opaque_preserve_case :
  precis_opaque_string [80; 97; 115; 115; 87; 111; 114; 100] =
  Some [80; 97; 115; 115; 87; 111; 114; 100].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: 空白文字を含む文字列 ("user name") の受容および保持検証。 *)
Lemma test_vector_opaque_preserve_space :
  precis_opaque_string [117; 115; 101; 114; 32; 110; 97; 109; 101] =
  Some [117; 115; 101; 114; 32; 110; 97; 109; 101].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: Latin 'A' (65) + 結合ダイエレシス (776) の合成文字 'Ä' (196) への正規化検証。 *)
Lemma test_vector_opaque_nfc_latin_a_diaeresis :
  precis_opaque_string [65; 776] = Some [196].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: Latin 'c' (99) + 結合セディラ (807) の合成文字 'ç' (231) への正規化検証。 *)
Lemma test_vector_opaque_nfc_latin_c_cedilla :
  precis_opaque_string [99; 807] = Some [231].
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: 空文字列拒絶 (None) の検証。 *)
Lemma test_vector_opaque_reject_empty :
  precis_opaque_string [] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: ASCII NUL 制御文字混入の拒絶 (None) 検証。 *)
Lemma test_vector_opaque_reject_nul :
  precis_opaque_string [0] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: 制御文字 (0x1F) 混入の拒絶 (None) 検証。 *)
Lemma test_vector_opaque_reject_control_1f :
  precis_opaque_string [31] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: Unicode サロゲートコードポイント (0xD800) の拒絶 (None) 検証。 *)
Lemma test_vector_opaque_reject_surrogate :
  precis_opaque_string [55296] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: 私用領域コードポイント (0xE000) の拒絶 (None) 検証。 *)
Lemma test_vector_opaque_reject_pua :
  precis_opaque_string [57344] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    OpaqueString テストベクタ: 非文字 (0xFFFF) の拒絶 (None) 検証。 *)
Lemma test_vector_opaque_reject_nonchar :
  precis_opaque_string [65535] = None.
Proof.
  reflexivity.
Qed.

(** [SPEC]
    プロファイル境界差分連立補題: 空白を含む同一文字列 ("user name") に対する受容・拒絶の境界検証。 *)
Lemma test_vector_profile_discrepancy_space :
  precis_username_case_mapped [117; 115; 101; 114; 32; 110; 97; 109; 101] = None /\
  precis_opaque_string [117; 115; 101; 114; 32; 110; 97; 109; 101] =
  Some [117; 115; 101; 114; 32; 110; 97; 109; 101].
Proof.
  split; reflexivity.
Qed.

(** [SPEC]
    プロファイル境界差分連立補題: 大文字を含む同一文字列 ("USER") に対する小文字化・大文字保持の境界検証。 *)
Lemma test_vector_profile_discrepancy_uppercase :
  precis_username_case_mapped [85; 83; 69; 82] = Some [117; 115; 101; 114] /\
  precis_opaque_string [85; 83; 69; 82] = Some [85; 83; 69; 82].
Proof.
  split; reflexivity.
Qed.

(** [SPEC]
    UsernameCaseMapped プロファイル正準化の計算的決定性定理。
    純粋関数型モデルにおいて、同一入力に対する正準化結果の一意性を数学的に保証する。 *)
Theorem username_case_mapped_deterministic : forall (s : PrecisString) (o1 o2 : option PrecisString),
  precis_username_case_mapped s = o1 ->
  precis_username_case_mapped s = o2 ->
  o1 = o2.
Proof.
  intros s o1 o2 H1 H2.
  rewrite <- H1.
  exact H2.
Qed.

(** [SPEC]
    OpaqueString プロファイル正準化の計算的決定性定理。
    純粋関数型モデルにおいて、同一入力に対する正準化結果の一意性を数学的に保証する。 *)
Theorem opaque_string_deterministic : forall (s : PrecisString) (o1 o2 : option PrecisString),
  precis_opaque_string s = o1 ->
  precis_opaque_string s = o2 ->
  o1 = o2.
Proof.
  intros s o1 o2 H1 H2.
  rewrite <- H1.
  exact H2.
Qed.

(** [MODEL]
    PRECIS テストケースレコード型。
    入力文字列と、各プロファイルに対する期待出力を保持する。 *)
Record PrecisTestCase : Type := {
  tc_input : PrecisString;
  tc_expected_user : option PrecisString;
  tc_expected_opaque : option PrecisString;
}.

(** [MODEL]
    テストケース妥当性判定述語。 *)
Definition test_case_valid (tc : PrecisTestCase) : Prop :=
  precis_username_case_mapped (tc_input tc) = tc_expected_user tc /\
  precis_opaque_string (tc_input tc) = tc_expected_opaque tc.

(** [MODEL]
    RFC 7564 / RFC 8265 既知テストベクタ集合 (Golden Test Suite)。 *)
Definition precis_golden_suite : list PrecisTestCase := [
  {| tc_input := [85; 115; 101; 114];
     tc_expected_user := Some [117; 115; 101; 114];
     tc_expected_opaque := Some [85; 115; 101; 114] |};
  {| tc_input := [85; 83; 69; 82];
     tc_expected_user := Some [117; 115; 101; 114];
     tc_expected_opaque := Some [85; 83; 69; 82] |};
  {| tc_input := [117; 115; 101; 114];
     tc_expected_user := Some [117; 115; 101; 114];
     tc_expected_opaque := Some [117; 115; 101; 114] |};
  {| tc_input := [927; 931];
     tc_expected_user := Some [959; 963];
     tc_expected_opaque := Some [927; 931] |};
  {| tc_input := [1048; 1074; 1072; 1085];
     tc_expected_user := Some [1080; 1074; 1072; 1085];
     tc_expected_opaque := Some [1048; 1074; 1072; 1085] |};
  {| tc_input := [201];
     tc_expected_user := Some [233];
     tc_expected_opaque := Some [201] |};
  {| tc_input := [117; 115; 101; 114; 32; 110; 97; 109; 101];
     tc_expected_user := None;
     tc_expected_opaque := Some [117; 115; 101; 114; 32; 110; 97; 109; 101] |};
  {| tc_input := [];
     tc_expected_user := None;
     tc_expected_opaque := None |};
  {| tc_input := [0];
     tc_expected_user := None;
     tc_expected_opaque := None |};
  {| tc_input := [9];
     tc_expected_user := None;
     tc_expected_opaque := None |};
  {| tc_input := [55296];
     tc_expected_user := None;
     tc_expected_opaque := None |};
  {| tc_input := [57344];
     tc_expected_user := None;
     tc_expected_opaque := None |};
  {| tc_input := [65535];
     tc_expected_user := None;
     tc_expected_opaque := None |};
  {| tc_input := [64976];
     tc_expected_user := None;
     tc_expected_opaque := None |};
  {| tc_input := [101; 769];
     tc_expected_user := Some [101; 769];
     tc_expected_opaque := Some [233] |};
  {| tc_input := [65; 776];
     tc_expected_user := Some [97; 776];
     tc_expected_opaque := Some [196] |};
  {| tc_input := [99; 807];
     tc_expected_user := Some [99; 807];
     tc_expected_opaque := Some [231] |};
  {| tc_input := [4352; 4449];
     tc_expected_user := Some [4352; 4449];
     tc_expected_opaque := Some [44032] |}
].

(** [SPEC]
    テストベクタ一括適合性定理 (Test Suite Conformance Theorem)。
    Golden Test Suite 内のすべてのテストケースにおいて、
    期待される正準化結果とモデルの計算結果が完全一致することを一括証明する。 *)
Theorem precis_golden_suite_conformance :
  Forall test_case_valid precis_golden_suite.
Proof.
  repeat (
    constructor; [
      split; reflexivity
    | ]
  ).
  constructor.
Qed.

End PrecisTestVectors.
