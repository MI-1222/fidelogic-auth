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
    intros H. inversion H; subst.
    cbn. apply Bool.andb_true_iff.
    split; [apply Bool.negb_true_iff; exact H2 | apply IH; exact H3].
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
