(** * TLVパーサー・シリアライザーのラウンドトリップ(可逆性)検証モジュール。 *)

From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.

From Fidelogic Require Import Tactics.
From Fidelogic.Aeneas Require Import Primitives.
Import Primitives.
From Fidelogic.Theories Require Import FidelogicCore.
Import FidelogicCore.
From Fidelogic.Theories Require Import TlvTotality.
Import TlvTotality.

Local Open Scope Z_scope.
Local Open Scope Primitives_scope.

(** ** スカラー比較に関する基礎補題 *)

(** [SPEC]
    スカラー型の小なり判定 (scalar_ltb) の非反射性。
    任意の x に対し (x s< x) は必ず false となる。 *)
Lemma scalar_ltb_irrefl : forall {ty : scalar_ty} (x : scalar ty),
  (scalar_ltb x x) = false.
Proof.
  intros ty x.
  unfold scalar_ltb.
  apply Z.ltb_irrefl.
Qed.

(** [SPEC]
    スカラー型の一致判定 (scalar_eqb) の反射性。
    任意の x に対し (x s= x) は必ず true となる。 *)
Lemma scalar_eqb_refl : forall {ty : scalar_ty} (x : scalar ty),
  (scalar_eqb x x) = true.
Proof.
  intros ty x.
  unfold scalar_eqb.
  apply Z.eqb_refl.
Qed.

(** [SPEC]
    スカラー型の非等価判定 (scalar_neqb) の非反射性。
    任意の x に対し (x s<> x) は必ず false となる。 *)
Lemma scalar_neqb_irrefl : forall {ty : scalar_ty} (x : scalar ty),
  (scalar_neqb x x) = false.
Proof.
  intros ty x.
  unfold scalar_neqb.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

(** [MODEL]
    空スライス表現。 *)
Definition slice_empty : slice u8 :=
  exist _ [] le_0_usize_max.

(** [MODEL]
    既知エントリペイロードの有効長条件。
    暗号文長 + 認証タグ長(16) が 1 バイト (255) 以下であること。 *)
Definition tlv_entry_payload_valid_len (ep : tlv_EntryPayload_t) : Prop :=
  to_Z (alloc_vec_Vec_len ep.(tlv_EntryPayload_ciphertext)) + 16 <= 255.

(** [SPEC]
    EntryPayload レコードの構成要素からの再構成補題。 *)
Lemma tlv_entry_payload_eta : forall (ep : tlv_EntryPayload_t),
  {| tlv_EntryPayload_ciphertext := ep.(tlv_EntryPayload_ciphertext);
     tlv_EntryPayload_auth_tag := ep.(tlv_EntryPayload_auth_tag) |} = ep.
Proof.
  destruct ep.
  reflexivity.
Qed.

(** ** レコード連鎖シリアライズ関係 (一般形) と単体への特殊化 *)

(** [MODEL]
    残余スライス rest を後続に伴う既知エントリシリアライズ関係。
    Rust 実装 serialize_record / serialize_record_into の出力スライスが満たす
    スライシング・インデックス・コピー操作の契約をモデル化する。 *)
Record tlv_is_serialized_entry_chain
  (ep : tlv_EntryPayload_t) (bytes rest : slice u8) : Type :=
mktlv_is_serialized_entry_chain {
  ser_chain_valid_len :
    tlv_entry_payload_valid_len ep;

  ser_chain_payload_len_u8 : u8;
  ser_chain_payload_len_usize : usize;
  ser_chain_total_len : usize;

  ser_chain_cast_len :
    scalar_cast U8 Usize ser_chain_payload_len_u8 = Ok ser_chain_payload_len_usize;
  ser_chain_add_total_len :
    usize_add 2%usize ser_chain_payload_len_usize = Ok ser_chain_total_len;

  ser_chain_header_parse :
    tlv_parse_tlv_header bytes =
      Ok (Some {| tlv_TlvHeader_tag := tlv_TAG_ENTRY;
                  tlv_TlvHeader_length := ser_chain_payload_len_u8 |});

  ser_chain_bytes_ge_total :
    (slice_len bytes s< ser_chain_total_len) = false;

  ser_chain_payload_bytes : slice u8;
  ser_chain_payload_bytes_len :
    slice_len ser_chain_payload_bytes = ser_chain_payload_len_usize;

  ser_chain_extract_payload :
    core_slice_index_Slice_index
      (core_slice_index_SliceIndexRangeUsizeSliceInst u8) bytes
      {|
        core_ops_range_Range_start := 2%usize;
        core_ops_range_Range_end_ := ser_chain_total_len
      |} = Ok ser_chain_payload_bytes;

  ser_chain_extract_rest :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8) bytes
      {|
        core_ops_range_RangeFrom_start := ser_chain_total_len
      |} = Ok rest;

  ser_chain_payload_len_ge_auth :
    (slice_len ser_chain_payload_bytes s< tlv_AUTH_TAG_LEN) = false;

  ser_chain_sub_ciphertext_len :
    usize_sub (slice_len ser_chain_payload_bytes) tlv_AUTH_TAG_LEN =
      Ok (alloc_vec_Vec_len ep.(tlv_EntryPayload_ciphertext));

  ser_chain_ct_slice : slice u8;
  ser_chain_extract_ciphertext :
    core_slice_index_Slice_index
      (core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
      ser_chain_payload_bytes
      {| core_ops_range_RangeTo_end_ := alloc_vec_Vec_len ep.(tlv_EntryPayload_ciphertext) |} =
    Ok ser_chain_ct_slice;

  ser_chain_restore_ciphertext :
    alloc_vec_Vec_Insts_CoreConvertFromShared0Slice_from
      core_clone_CloneU8 ser_chain_ct_slice =
    Ok ep.(tlv_EntryPayload_ciphertext);

  ser_chain_tag_slice : slice u8;
  ser_chain_extract_tag :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
      ser_chain_payload_bytes
      {| core_ops_range_RangeFrom_start := alloc_vec_Vec_len ep.(tlv_EntryPayload_ciphertext) |} =
    Ok ser_chain_tag_slice;

  ser_chain_tag_copied_slice : slice u8;
  ser_chain_copy_tag :
    core_slice_Slice_copy_from_slice
      core_marker_CopyU8
      (array_to_slice (array_repeat 16%usize 0%u8))
      ser_chain_tag_slice =
    Ok ser_chain_tag_copied_slice;

  ser_chain_restore_tag :
    array_from_slice (array_repeat 16%usize 0%u8) ser_chain_tag_copied_slice =
    ep.(tlv_EntryPayload_auth_tag);
}.

(** [MODEL]
    残余スライス rest を後続に伴う未知タグシリアライズ関係。
    Rust 実装 serialize_record の TlvRecord::Unknown 分岐に対応する。 *)
Record tlv_is_serialized_unknown_chain
  (tag : u8) (raw_bytes : alloc_vec_Vec u8) (bytes rest : slice u8) : Type :=
mktlv_is_serialized_unknown_chain {
  ser_unk_chain_valid_len :
    to_Z (alloc_vec_Vec_len raw_bytes) <= 255;

  ser_unk_chain_tag_not_entry :
    (tag s= tlv_TAG_ENTRY) = false;

  ser_unk_chain_payload_len_u8 : u8;
  ser_unk_chain_payload_len_usize : usize;
  ser_unk_chain_total_len : usize;

  ser_unk_chain_cast_len :
    scalar_cast U8 Usize ser_unk_chain_payload_len_u8 = Ok ser_unk_chain_payload_len_usize;
  ser_unk_chain_add_total_len :
    usize_add 2%usize ser_unk_chain_payload_len_usize = Ok ser_unk_chain_total_len;

  ser_unk_chain_header_parse :
    tlv_parse_tlv_header bytes =
      Ok (Some {| tlv_TlvHeader_tag := tag;
                  tlv_TlvHeader_length := ser_unk_chain_payload_len_u8 |});

  ser_unk_chain_bytes_ge_total :
    (slice_len bytes s< ser_unk_chain_total_len) = false;

  ser_unk_chain_payload_bytes : slice u8;
  ser_unk_chain_payload_bytes_len :
    slice_len ser_unk_chain_payload_bytes = ser_unk_chain_payload_len_usize;

  ser_unk_chain_extract_payload :
    core_slice_index_Slice_index
      (core_slice_index_SliceIndexRangeUsizeSliceInst u8) bytes
      {|
        core_ops_range_Range_start := 2%usize;
        core_ops_range_Range_end_ := ser_unk_chain_total_len
      |} = Ok ser_unk_chain_payload_bytes;

  ser_unk_chain_extract_rest :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8) bytes
      {|
        core_ops_range_RangeFrom_start := ser_unk_chain_total_len
      |} = Ok rest;

  ser_unk_chain_restore_raw_bytes :
    alloc_vec_Vec_Insts_CoreConvertFromShared0Slice_from
      core_clone_CloneU8 ser_unk_chain_payload_bytes =
    Ok raw_bytes;
}.

(** [MODEL]
    残余スライス rest を後続に伴うレコード単体の直和型シリアライズ関係。 *)
Inductive tlv_is_serialized_record_chain : tlv_TlvRecord_t -> slice u8 -> slice u8 -> Type :=
| Tlv_is_serialized_record_chain_Entry :
    forall (ep : tlv_EntryPayload_t) (bytes rest : slice u8),
      tlv_is_serialized_entry_chain ep bytes rest ->
      tlv_is_serialized_record_chain (Tlv_TlvRecord_Entry ep) bytes rest
| Tlv_is_serialized_record_chain_Unknown :
    forall (tag : u8) (raw_bytes : alloc_vec_Vec u8) (bytes rest : slice u8),
      tlv_is_serialized_unknown_chain tag raw_bytes bytes rest ->
      tlv_is_serialized_record_chain (Tlv_TlvRecord_Unknown tag raw_bytes) bytes rest.

(** [SPEC]
    補題 10: 残余スライスを保持する単一 TlvRecord に対するラウンドトリップ補題。 *)
Lemma tlv_record_chain_roundtrip :
  forall (r : tlv_TlvRecord_t) (bytes rest : slice u8),
    tlv_is_serialized_record_chain r bytes rest ->
    tlv_deserialize_record bytes =
      Ok (Core_result_Result_Ok (r, rest)).
Proof.
  intros r bytes rest Hrec.
  destruct Hrec as [ep b rst Hser | tag raw_bytes b rst Hser].
  - (* 既知エントリ *)
    unfold tlv_deserialize_record.
    rewrite (ser_chain_header_parse ep b rst Hser); cbn [bind].
    change (tlv_TlvHeader_length {| tlv_TlvHeader_tag := tlv_TAG_ENTRY; tlv_TlvHeader_length := ser_chain_payload_len_u8 ep b rst Hser |})
      with (ser_chain_payload_len_u8 ep b rst Hser).
    rewrite (ser_chain_cast_len ep b rst Hser); cbn [bind].
    rewrite (ser_chain_add_total_len ep b rst Hser); cbn [bind].
    rewrite (ser_chain_bytes_ge_total ep b rst Hser); cbn [bind].
    rewrite (ser_chain_extract_payload ep b rst Hser); cbn [bind].
    change (core_ops_range_RangeFrom_t (scalar Usize)) with (core_ops_range_RangeFrom_t usize).
    change (@mkcore_ops_range_RangeFrom_t (scalar Usize)) with (@mkcore_ops_range_RangeFrom_t usize).
    rewrite (ser_chain_extract_rest ep b rst Hser); cbn [bind].
    change (tlv_TlvHeader_tag {| tlv_TlvHeader_tag := tlv_TAG_ENTRY; tlv_TlvHeader_length := ser_chain_payload_len_u8 ep b rst Hser |})
      with tlv_TAG_ENTRY.
    rewrite (scalar_eqb_refl tlv_TAG_ENTRY).
    rewrite (ser_chain_payload_len_ge_auth ep b rst Hser); cbn [bind].
    rewrite (ser_chain_sub_ciphertext_len ep b rst Hser); cbn [bind].
    change (core_ops_range_RangeTo (scalar Usize)) with (core_ops_range_RangeTo usize).
    change (@mk_core_ops_range_RangeTo (scalar Usize)) with (@mk_core_ops_range_RangeTo usize).
    rewrite (ser_chain_extract_ciphertext ep b rst Hser); cbn [bind].
    rewrite (ser_chain_restore_ciphertext ep b rst Hser); cbn [bind].
    rewrite (ser_chain_extract_tag ep b rst Hser); cbn [bind].
    unfold array_to_slice_mut.
    rewrite (ser_chain_copy_tag ep b rst Hser); cbn [bind].
    rewrite (ser_chain_restore_tag ep b rst Hser).
    unfold tlv_EntryPayload_new.
    rewrite (tlv_entry_payload_eta ep).
    reflexivity.
  - (* 未知タグ *)
    unfold tlv_deserialize_record.
    rewrite (ser_unk_chain_header_parse tag raw_bytes b rst Hser); cbn [bind].
    change (tlv_TlvHeader_length {| tlv_TlvHeader_tag := tag; tlv_TlvHeader_length := ser_unk_chain_payload_len_u8 tag raw_bytes b rst Hser |})
      with (ser_unk_chain_payload_len_u8 tag raw_bytes b rst Hser).
    rewrite (ser_unk_chain_cast_len tag raw_bytes b rst Hser); cbn [bind].
    rewrite (ser_unk_chain_add_total_len tag raw_bytes b rst Hser); cbn [bind].
    rewrite (ser_unk_chain_bytes_ge_total tag raw_bytes b rst Hser); cbn [bind].
    rewrite (ser_unk_chain_extract_payload tag raw_bytes b rst Hser); cbn [bind].
    change (core_ops_range_RangeFrom_t (scalar Usize)) with (core_ops_range_RangeFrom_t usize).
    change (@mkcore_ops_range_RangeFrom_t (scalar Usize)) with (@mkcore_ops_range_RangeFrom_t usize).
    rewrite (ser_unk_chain_extract_rest tag raw_bytes b rst Hser); cbn [bind].
    change (tlv_TlvHeader_tag {| tlv_TlvHeader_tag := tag; tlv_TlvHeader_length := ser_unk_chain_payload_len_u8 tag raw_bytes b rst Hser |})
      with tag.
    rewrite (ser_unk_chain_tag_not_entry tag raw_bytes b rst Hser).
    rewrite (ser_unk_chain_restore_raw_bytes tag raw_bytes b rst Hser).
    reflexivity.
Qed.

(** [MODEL]
    単体既知エントリシリアライズ関係 (残余スライスを slice_empty に特殊化)。 *)
Definition tlv_is_serialized_entry
  (ep : tlv_EntryPayload_t) (bytes : slice u8) : Type :=
  tlv_is_serialized_entry_chain ep bytes slice_empty.

(** ヘッダー宣言および補題との後方互換性のための射影関数。 *)
Definition ser_payload_len_u8
  (ep : tlv_EntryPayload_t) (bytes : slice u8)
  (Hser : tlv_is_serialized_entry ep bytes) : u8 :=
  ser_chain_payload_len_u8 ep bytes slice_empty Hser.

(** [MODEL]
    単体未知タグシリアライズ関係 (残余スライスを slice_empty に特殊化)。 *)
Definition tlv_is_serialized_unknown
  (tag : u8) (raw_bytes : alloc_vec_Vec u8) (bytes : slice u8) : Type :=
  tlv_is_serialized_unknown_chain tag raw_bytes bytes slice_empty.

(** [MODEL]
    レコード全体のシリアライズ関係 (既知エントリおよび未知タグの直和型)。 *)
Inductive tlv_is_serialized_record : tlv_TlvRecord_t -> slice u8 -> Type :=
| Tlv_is_serialized_record_Entry :
    forall (ep : tlv_EntryPayload_t) (bytes : slice u8),
      tlv_is_serialized_entry ep bytes ->
      tlv_is_serialized_record (Tlv_TlvRecord_Entry ep) bytes
| Tlv_is_serialized_record_Unknown :
    forall (tag : u8) (raw_bytes : alloc_vec_Vec u8) (bytes : slice u8),
      tlv_is_serialized_unknown tag raw_bytes bytes ->
      tlv_is_serialized_record (Tlv_TlvRecord_Unknown tag raw_bytes) bytes.

(** [SPEC]
    補題 1: 既知タグエントリに対するヘッダーパースの整合性。 *)
Lemma tlv_parse_header_of_serialized_entry :
  forall (ep : tlv_EntryPayload_t) (bytes : slice u8) (Hser : tlv_is_serialized_entry ep bytes),
    tlv_parse_tlv_header bytes =
      Ok (Some {| tlv_TlvHeader_tag := tlv_TAG_ENTRY;
                  tlv_TlvHeader_length := (ser_payload_len_u8 ep bytes Hser) |}).
Proof.
  intros ep bytes Hser.
  exact (ser_chain_header_parse ep bytes slice_empty Hser).
Qed.

(** [SPEC]
    補題 2: 既知タグエントリに対する最小ラウンドトリップ補題。
    既知エントリペイロード ep をシリアライズしたバイト列 bytes に対し、
    tlv_deserialize_record を実行すると、元のエントリレコードと空の残余スライスが
    完全に復元される。 *)
Lemma tlv_record_roundtrip_entry_minimal :
  forall (ep : tlv_EntryPayload_t) (bytes : slice u8),
    tlv_is_serialized_entry ep bytes ->
    tlv_deserialize_record bytes =
      Ok (Core_result_Result_Ok (Tlv_TlvRecord_Entry ep, slice_empty)).
Proof.
  intros ep bytes Hser.
  apply (tlv_record_chain_roundtrip (Tlv_TlvRecord_Entry ep) bytes slice_empty).
  apply Tlv_is_serialized_record_chain_Entry.
  exact Hser.
Qed.

(** [SPEC]
    補題 3: TlvRecord レベルでの既知タグ最小ラウンドトリップ補題。 *)
Lemma tlv_record_roundtrip_known :
  forall (ep : tlv_EntryPayload_t) (bytes : slice u8),
    tlv_is_serialized_record (Tlv_TlvRecord_Entry ep) bytes ->
    tlv_deserialize_record bytes =
      Ok (Core_result_Result_Ok (Tlv_TlvRecord_Entry ep, slice_empty)).
Proof.
  intros ep bytes Hrec.
  inversion Hrec; subst.
  apply tlv_record_roundtrip_entry_minimal.
  assumption.
Qed.

(** [SPEC]
    補題 4: 未知タグレコードに対する最小ラウンドトリップ補題。
    未知タグレコード (tag, raw_bytes) をシリアライズしたバイト列 bytes に対し、
    tlv_deserialize_record を実行すると、
    元の未知タグレコードと空の残余スライスが完全に復元される。 *)
Lemma tlv_record_roundtrip_unknown_minimal :
  forall (tag : u8) (raw_bytes : alloc_vec_Vec u8) (bytes : slice u8),
    tlv_is_serialized_unknown tag raw_bytes bytes ->
    tlv_deserialize_record bytes =
      Ok (Core_result_Result_Ok (Tlv_TlvRecord_Unknown tag raw_bytes, slice_empty)).
Proof.
  intros tag raw_bytes bytes Hser.
  apply (tlv_record_chain_roundtrip (Tlv_TlvRecord_Unknown tag raw_bytes) bytes slice_empty).
  apply Tlv_is_serialized_record_chain_Unknown.
  exact Hser.
Qed.

(** [SPEC]
    補題 5: TlvRecord レベルでの未知タグ最小ラウンドトリップ補題。 *)
Lemma tlv_record_roundtrip_unknown :
  forall (tag : u8) (raw_bytes : alloc_vec_Vec u8) (bytes : slice u8),
    tlv_is_serialized_record (Tlv_TlvRecord_Unknown tag raw_bytes) bytes ->
    tlv_deserialize_record bytes =
      Ok (Core_result_Result_Ok (Tlv_TlvRecord_Unknown tag raw_bytes, slice_empty)).
Proof.
  intros tag raw_bytes bytes Hrec.
  inversion Hrec; subst.
  apply tlv_record_roundtrip_unknown_minimal.
  assumption.
Qed.

(** ** VaultHeader のラウンドトリップ検証 *)

(** [SPEC]
    VaultHeader レコードの構成要素からの再構成補題。 *)
Lemma tlv_vault_header_eta : forall (h : tlv_VaultHeader_t),
  {| tlv_VaultHeader_magic := h.(tlv_VaultHeader_magic);
     tlv_VaultHeader_version := h.(tlv_VaultHeader_version);
     tlv_VaultHeader_suite_id := h.(tlv_VaultHeader_suite_id) |} = h.
Proof.
  destruct h.
  reflexivity.
Qed.

(** [MODEL]
    残余スライス rest を後続に伴う VaultHeader シリアライズ関係。
    有効なマジックバイト ("FVAU") を保持し、6バイト固定長のヘッダー構造を満たすことを規定する。 *)
Record tlv_is_serialized_header_chain
  (h : tlv_VaultHeader_t) (bytes rest : slice u8) : Type :=
mktlv_is_serialized_header_chain {
  ser_hdr_chain_valid_magic :
    h.(tlv_VaultHeader_magic) = tlv_VAULT_MAGIC;

  ser_hdr_chain_bytes_ge_hdr :
    (slice_len bytes s< tlv_VAULT_HEADER_LEN) = false;

  ser_hdr_chain_b0 : u8;
  ser_hdr_chain_b1 : u8;
  ser_hdr_chain_b2 : u8;
  ser_hdr_chain_b3 : u8;

  ser_hdr_chain_idx0 : slice_index_usize bytes 0%usize = Ok ser_hdr_chain_b0;
  ser_hdr_chain_idx1 : slice_index_usize bytes 1%usize = Ok ser_hdr_chain_b1;
  ser_hdr_chain_idx2 : slice_index_usize bytes 2%usize = Ok ser_hdr_chain_b2;
  ser_hdr_chain_idx3 : slice_index_usize bytes 3%usize = Ok ser_hdr_chain_b3;
  ser_hdr_chain_idx4 : slice_index_usize bytes 4%usize = Ok h.(tlv_VaultHeader_version);
  ser_hdr_chain_idx5 : slice_index_usize bytes 5%usize = Ok h.(tlv_VaultHeader_suite_id);

  ser_hdr_chain_reconstruct_magic :
    mk_array 4%usize [ser_hdr_chain_b0; ser_hdr_chain_b1; ser_hdr_chain_b2; ser_hdr_chain_b3] = tlv_VAULT_MAGIC;

  ser_hdr_chain_magic_idx0 : array_index_usize tlv_VAULT_MAGIC 0%usize = Ok ser_hdr_chain_b0;
  ser_hdr_chain_magic_idx1 : array_index_usize tlv_VAULT_MAGIC 1%usize = Ok ser_hdr_chain_b1;
  ser_hdr_chain_magic_idx2 : array_index_usize tlv_VAULT_MAGIC 2%usize = Ok ser_hdr_chain_b2;
  ser_hdr_chain_magic_idx3 : array_index_usize tlv_VAULT_MAGIC 3%usize = Ok ser_hdr_chain_b3;

  ser_hdr_chain_extract_rest :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8) bytes
      {| core_ops_range_RangeFrom_start := tlv_VAULT_HEADER_LEN |} = Ok rest;
}.

(** [SPEC]
    補題 7: 残余スライスを保持する VaultHeader に対するラウンドトリップ補題。 *)
Lemma tlv_header_chain_roundtrip :
  forall (h : tlv_VaultHeader_t) (bytes rest : slice u8),
    tlv_is_serialized_header_chain h bytes rest ->
    tlv_deserialize_header bytes =
      Ok (Core_result_Result_Ok (h, rest)).
Proof.
  intros h bytes rest Hser.
  unfold tlv_deserialize_header.
  rewrite (ser_hdr_chain_bytes_ge_hdr h bytes rest Hser).
  cbn [bind].
  rewrite (ser_hdr_chain_idx0 h bytes rest Hser); cbn [bind].
  rewrite (ser_hdr_chain_idx1 h bytes rest Hser); cbn [bind].
  rewrite (ser_hdr_chain_idx2 h bytes rest Hser); cbn [bind].
  rewrite (ser_hdr_chain_idx3 h bytes rest Hser); cbn [bind].
  rewrite (ser_hdr_chain_reconstruct_magic h bytes rest Hser).
  rewrite (ser_hdr_chain_magic_idx0 h bytes rest Hser); cbn [bind].
  rewrite (scalar_neqb_irrefl (ser_hdr_chain_b0 h bytes rest Hser)).
  rewrite (ser_hdr_chain_magic_idx1 h bytes rest Hser); cbn [bind].
  rewrite (scalar_neqb_irrefl (ser_hdr_chain_b1 h bytes rest Hser)).
  rewrite (ser_hdr_chain_magic_idx2 h bytes rest Hser); cbn [bind].
  rewrite (scalar_neqb_irrefl (ser_hdr_chain_b2 h bytes rest Hser)).
  rewrite (ser_hdr_chain_magic_idx3 h bytes rest Hser); cbn [bind].
  rewrite (scalar_neqb_irrefl (ser_hdr_chain_b3 h bytes rest Hser)).
  rewrite (ser_hdr_chain_idx4 h bytes rest Hser); cbn [bind].
  rewrite (ser_hdr_chain_idx5 h bytes rest Hser); cbn [bind].
  change (core_ops_range_RangeFrom_t (scalar Usize)) with (core_ops_range_RangeFrom_t usize).
  change (@mkcore_ops_range_RangeFrom_t (scalar Usize)) with (@mkcore_ops_range_RangeFrom_t usize).
  rewrite (ser_hdr_chain_extract_rest h bytes rest Hser); cbn [bind].
  rewrite <- (ser_hdr_chain_valid_magic h bytes rest Hser).
  rewrite (tlv_vault_header_eta h).
  reflexivity.
Qed.

(** [MODEL]
    単体 VaultHeader シリアライズ関係 (残余スライスを slice_empty に特殊化)。 *)
Definition tlv_is_serialized_header
  (h : tlv_VaultHeader_t) (bytes : slice u8) : Type :=
  tlv_is_serialized_header_chain h bytes slice_empty.

(** [SPEC]
    補題 6: VaultHeader に対する最小ラウンドトリップ補題。
    有効なマジックバイトを持つ VaultHeader h をシリアライズしたバイト列 bytes に対し、
    tlv_deserialize_header を実行すると、
    元のヘッダー h と空の残余スライスが完全に復元される。 *)
Lemma tlv_header_roundtrip :
  forall (h : tlv_VaultHeader_t) (bytes : slice u8),
    tlv_is_serialized_header h bytes ->
    tlv_deserialize_header bytes =
      Ok (Core_result_Result_Ok (h, slice_empty)).
Proof.
  intros h bytes Hser.
  apply (tlv_header_chain_roundtrip h bytes slice_empty Hser).
Qed.

(** [SPEC]
    VaultHeader シリアライザーの評価計算補題。
    有効なマジックバイトを持つ VaultHeader h に対し、tlv_serialize_header は必ず成功し、
    マジック 4 バイト、バージョン、暗号スイートIDから成る 6 バイト配列を返す。 *)
Lemma tlv_serialize_header_eval :
  forall (h : tlv_VaultHeader_t),
    h.(tlv_VaultHeader_magic) = tlv_VAULT_MAGIC ->
    tlv_serialize_header h =
      Ok (mk_array 6%usize [
            70%u8; 86%u8; 65%u8; 85%u8;
            h.(tlv_VaultHeader_version);
            h.(tlv_VaultHeader_suite_id)
         ]).
Proof.
  intros h Hmagic.
  unfold tlv_serialize_header.
  rewrite Hmagic.
  unfold tlv_VAULT_MAGIC.
  erewrite (mk_array_index_nth _ _ _ _); [| reflexivity ].
  cbn [bind].
  erewrite (mk_array_index_nth _ _ _ _); [| reflexivity ].
  cbn [bind].
  erewrite (mk_array_index_nth _ _ _ _); [| reflexivity ].
  cbn [bind].
  erewrite (mk_array_index_nth _ _ _ _); [| reflexivity ].
  cbn [bind].
  reflexivity.
Qed.

(** [SPEC]
    VaultHeader シリアライザーのシリアライズ関係充足補題 (構成的実在性 / Realizability)。
    有効なマジックバイトを持つ VaultHeader h に対し、tlv_serialize_header が出力する 6 バイト配列を
    スライス化したバイト列は、前提 Record (tlv_is_serialized_header) の全契約を満たす。
    これにより、tlv_is_serialized_header が空虚な仮定ではなく、Rust シリアライザーによって
    構成的に充足されることが保証される。 *)
Lemma tlv_serialize_header_is_serialized :
  forall (h : tlv_VaultHeader_t) (serialized : array u8 6%usize),
    h.(tlv_VaultHeader_magic) = tlv_VAULT_MAGIC ->
    tlv_serialize_header h = Ok serialized ->
    tlv_is_serialized_header h (array_to_slice serialized).
Proof.
  intros h serialized Hmagic Hser.
  pose proof (tlv_serialize_header_eval h Hmagic) as Heval.
  rewrite Heval in Hser.
  inv Hser.
  refine {|
    ser_hdr_chain_valid_magic := Hmagic;
    ser_hdr_chain_bytes_ge_hdr := _;
    ser_hdr_chain_b0 := 70%u8;
    ser_hdr_chain_b1 := 86%u8;
    ser_hdr_chain_b2 := 65%u8;
    ser_hdr_chain_b3 := 85%u8;
    ser_hdr_chain_idx0 := _;
    ser_hdr_chain_idx1 := _;
    ser_hdr_chain_idx2 := _;
    ser_hdr_chain_idx3 := _;
    ser_hdr_chain_idx4 := _;
    ser_hdr_chain_idx5 := _;
    ser_hdr_chain_reconstruct_magic := _;
    ser_hdr_chain_magic_idx0 := _;
    ser_hdr_chain_magic_idx1 := _;
    ser_hdr_chain_magic_idx2 := _;
    ser_hdr_chain_magic_idx3 := _;
    ser_hdr_chain_extract_rest := _
  |}.
  - rewrite array_to_slice_len.
    apply scalar_ltb_irrefl.
  - rewrite array_to_slice_index.
    apply (mk_array_index_nth 6%usize _ 0%usize 70%u8); reflexivity.
  - rewrite array_to_slice_index.
    apply (mk_array_index_nth 6%usize _ 1%usize 86%u8); reflexivity.
  - rewrite array_to_slice_index.
    apply (mk_array_index_nth 6%usize _ 2%usize 65%u8); reflexivity.
  - rewrite array_to_slice_index.
    apply (mk_array_index_nth 6%usize _ 3%usize 85%u8); reflexivity.
  - rewrite array_to_slice_index.
    apply (mk_array_index_nth 6%usize _ 4%usize (tlv_VaultHeader_version h)); reflexivity.
  - rewrite array_to_slice_index.
    apply (mk_array_index_nth 6%usize _ 5%usize (tlv_VaultHeader_suite_id h)); reflexivity.
  - unfold tlv_VAULT_MAGIC. reflexivity.
  - unfold tlv_VAULT_MAGIC.
    apply (mk_array_index_nth 4%usize _ 0%usize 70%u8); reflexivity.
  - unfold tlv_VAULT_MAGIC.
    apply (mk_array_index_nth 4%usize _ 1%usize 86%u8); reflexivity.
  - unfold tlv_VAULT_MAGIC.
    apply (mk_array_index_nth 4%usize _ 2%usize 65%u8); reflexivity.
  - unfold tlv_VAULT_MAGIC.
    apply (mk_array_index_nth 4%usize _ 3%usize 85%u8); reflexivity.
  - apply array_to_slice_range_from_end.
Qed.

(** [SPEC]
    最上位完全定理: VaultHeader の真のラウンドトリップ定理。
    有効なマジックバイトを持つ VaultHeader h に対し、tlv_serialize_header でシリアライズした配列 serialized を
    スライス化したバイト列 (array_to_slice serialized) を tlv_deserialize_header でデシリアライズすると、
    元の VaultHeader h と空の残余スライスが完全に復元される。
    (Rust シリアライズ関数とデシリアライズ関数の真の関数合成を直接検証する)。 *)
Theorem tlv_header_roundtrip_sound :
  forall (h : tlv_VaultHeader_t) (serialized : array u8 6%usize),
    h.(tlv_VaultHeader_magic) = tlv_VAULT_MAGIC ->
    tlv_serialize_header h = Ok serialized ->
    tlv_deserialize_header (array_to_slice serialized) =
      Ok (Core_result_Result_Ok (h, slice_empty)).
Proof.
  intros h serialized Hmagic Hser.
  apply tlv_header_roundtrip.
  apply (tlv_serialize_header_is_serialized h serialized Hmagic Hser).
Qed.

(** ** KEKスロット単体およびスロット列のラウンドトリップ検証 *)

(** [SPEC]
    KekSlotEntry レコードの構成要素からの再構成補題。 *)
Lemma tlv_kek_slot_entry_eta : forall (slot : tlv_KekSlotEntry_t),
  {| tlv_KekSlotEntry_slot_id := slot.(tlv_KekSlotEntry_slot_id);
     tlv_KekSlotEntry_kdf_kind := slot.(tlv_KekSlotEntry_kdf_kind);
     tlv_KekSlotEntry_wrapped_dek_len := slot.(tlv_KekSlotEntry_wrapped_dek_len);
     tlv_KekSlotEntry_wrapped_dek := slot.(tlv_KekSlotEntry_wrapped_dek) |} = slot.
Proof.
  destruct slot.
  reflexivity.
Qed.

(** [MODEL]
    KekSlotEntry に対するシリアライズ結果バイト列 bytes の振る舞い規定。 *)
Record tlv_is_serialized_slot
  (slot : tlv_KekSlotEntry_t) (bytes rest : slice u8) : Type :=
mktlv_is_serialized_slot {
  ser_slot_bytes_ge_hdr :
    (slice_len bytes s< tlv_KEK_SLOT_HEADER_LEN) = false;

  ser_slot_idx0 :
    slice_index_usize bytes 0%usize = Ok slot.(tlv_KekSlotEntry_slot_id);
  ser_slot_idx1 :
    slice_index_usize bytes 1%usize = Ok slot.(tlv_KekSlotEntry_kdf_kind);

  ser_slot_b2 : u8;
  ser_slot_b3 : u8;

  ser_slot_idx2 :
    slice_index_usize bytes 2%usize = Ok ser_slot_b2;
  ser_slot_idx3 :
    slice_index_usize bytes 3%usize = Ok ser_slot_b3;

  ser_slot_reconstruct_len :
    core_num_U16_from_be_bytes (mk_array 2%usize [ser_slot_b2; ser_slot_b3]) =
      slot.(tlv_KekSlotEntry_wrapped_dek_len);

  ser_slot_dek_len_usize : usize;
  ser_slot_cast_dek_len :
    scalar_cast U16 Usize slot.(tlv_KekSlotEntry_wrapped_dek_len) =
      Ok ser_slot_dek_len_usize;

  ser_slot_payload_bytes : slice u8;
  ser_slot_extract_payload :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8) bytes
      {| core_ops_range_RangeFrom_start := tlv_KEK_SLOT_HEADER_LEN |} =
    Ok ser_slot_payload_bytes;

  ser_slot_payload_len_ge_dek :
    (slice_len ser_slot_payload_bytes s< ser_slot_dek_len_usize) = false;

  ser_slot_dek_slice : slice u8;
  ser_slot_extract_dek :
    core_slice_index_Slice_index
      (core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
      ser_slot_payload_bytes
      {| core_ops_range_RangeTo_end_ := ser_slot_dek_len_usize |} =
    Ok ser_slot_dek_slice;

  ser_slot_restore_dek :
    alloc_slice_Slice_to_vec core_clone_CloneU8 ser_slot_dek_slice =
      Ok slot.(tlv_KekSlotEntry_wrapped_dek);

  ser_slot_extract_rest :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
      ser_slot_payload_bytes
      {| core_ops_range_RangeFrom_start := ser_slot_dek_len_usize |} =
    Ok rest;
}.

(** [SPEC]
    補題 8: 単一 KekSlotEntry に対するラウンドトリップ補題。 *)
Lemma tlv_slot_roundtrip :
  forall (slot : tlv_KekSlotEntry_t) (bytes rest : slice u8),
    tlv_is_serialized_slot slot bytes rest ->
    tlv_deserialize_slot_entry bytes =
      Ok (Core_result_Result_Ok (slot, rest)).
Proof.
  intros slot bytes rest Hser.
  unfold tlv_deserialize_slot_entry.
  rewrite (ser_slot_bytes_ge_hdr slot bytes rest Hser).
  cbn [bind].
  rewrite (ser_slot_idx0 slot bytes rest Hser); cbn [bind].
  rewrite (ser_slot_idx1 slot bytes rest Hser); cbn [bind].
  rewrite (ser_slot_idx2 slot bytes rest Hser); cbn [bind].
  rewrite (ser_slot_idx3 slot bytes rest Hser); cbn [bind].
  rewrite (ser_slot_reconstruct_len slot bytes rest Hser).
  rewrite (ser_slot_cast_dek_len slot bytes rest Hser); cbn [bind].
  change (core_ops_range_RangeFrom_t (scalar Usize)) with (core_ops_range_RangeFrom_t usize).
  change (@mkcore_ops_range_RangeFrom_t (scalar Usize)) with (@mkcore_ops_range_RangeFrom_t usize).
  rewrite (ser_slot_extract_payload slot bytes rest Hser); cbn [bind].
  rewrite (ser_slot_payload_len_ge_dek slot bytes rest Hser).
  cbn [bind].
  change (core_ops_range_RangeTo (scalar Usize)) with (core_ops_range_RangeTo usize).
  change (@mk_core_ops_range_RangeTo (scalar Usize)) with (@mk_core_ops_range_RangeTo usize).
  rewrite (ser_slot_extract_dek slot bytes rest Hser); cbn [bind].
  rewrite (ser_slot_restore_dek slot bytes rest Hser); cbn [bind].
  rewrite (ser_slot_extract_rest slot bytes rest Hser); cbn [bind].
  rewrite (tlv_kek_slot_entry_eta slot).
  reflexivity.
Qed.

(** [MODEL]
    スロットリストに対する帰納的シリアライズ関係。 *)
Inductive tlv_is_serialized_slots : list tlv_KekSlotEntry_t -> slice u8 -> slice u8 -> Type :=
| Tlv_is_serialized_slots_nil :
    forall (bytes : slice u8),
      tlv_is_serialized_slots [] bytes bytes
| Tlv_is_serialized_slots_cons :
    forall (slot : tlv_KekSlotEntry_t) (slots : list tlv_KekSlotEntry_t)
           (bytes mid rest : slice u8),
      tlv_is_serialized_slot slot bytes mid ->
      tlv_is_serialized_slots slots mid rest ->
      tlv_is_serialized_slots (slot :: slots) bytes rest.

(** [SPEC]
    補題 9: スロットリスト全体に対するリスト帰納的ラウンドトリップ補題。 *)
Lemma tlv_slots_roundtrip :
  forall (slots : list tlv_KekSlotEntry_t) (bytes rest : slice u8),
    tlv_is_serialized_slots slots bytes rest ->
    tlv_deserialize_slots (length slots) bytes =
      Ok (Core_result_Result_Ok (slots, rest)).
Proof.
  intros slots bytes rest Hser.
  induction Hser as [b | slot slots' b mid r Hslot Hslots' IH].
  - reflexivity.
  - cbn [tlv_deserialize_slots length].
    unfold bind.
    rewrite (tlv_slot_roundtrip slot b mid Hslot).
    cbn [bind].
    rewrite IH.
    reflexivity.
Qed.

(** ** 未知タグ・既知タグ混在レコード列の連鎖シリアライズ関係とラウンドトリップ検証 *)

(** [MODEL]
    混在レコードリストに対する帰納的シリアライズ関係。 *)
Inductive tlv_is_serialized_records : list tlv_TlvRecord_t -> slice u8 -> slice u8 -> Type :=
| Tlv_is_serialized_records_nil :
    forall (bytes : slice u8),
      tlv_is_serialized_records [] bytes bytes
| Tlv_is_serialized_records_cons :
    forall (r : tlv_TlvRecord_t) (records : list tlv_TlvRecord_t)
           (bytes mid rest : slice u8),
      tlv_is_serialized_record_chain r bytes mid ->
      tlv_is_serialized_records records mid rest ->
      tlv_is_serialized_records (r :: records) bytes rest.

(** [SPEC]
    補題 11: 未知・既知混在レコードリスト全体に対するリスト帰納的ラウンドトリップ補題。 *)
Lemma tlv_records_roundtrip :
  forall (records : list tlv_TlvRecord_t) (bytes rest : slice u8),
    tlv_is_serialized_records records bytes rest ->
    tlv_deserialize_records (length records) bytes =
      Ok (Core_result_Result_Ok (records, rest)).
Proof.
  intros records bytes rest Hser.
  induction Hser as [b | r rs b mid rst Hr Hrs IH].
  - reflexivity.
  - cbn [tlv_deserialize_records length].
    unfold bind.
    rewrite (tlv_record_chain_roundtrip r b mid Hr).
    cbn [bind].
    rewrite IH.
    reflexivity.
Qed.

(** ** Vault 全体のラウンドトリップ検証 *)

(** [SPEC]
    Vault レコードの構成要素からの再構成補題。 *)
Lemma tlv_vault_eta : forall (v : tlv_Vault_t),
  {| tlv_Vault_header := v.(tlv_Vault_header);
     tlv_Vault_slots := v.(tlv_Vault_slots);
     tlv_Vault_records := v.(tlv_Vault_records) |} = v.
Proof.
  destruct v.
  reflexivity.
Qed.

(** [MODEL]
    未知タグと既知タグが混在する Vault 構造全体に対するシリアライズ結果バイト列 bytes の振る舞い規定。 *)
Record tlv_is_serialized_vault
  (v : tlv_Vault_t) (bytes : slice u8) : Type :=
mktlv_is_serialized_vault {
  ser_vault_rest1 : slice u8;
  ser_vault_header :
    tlv_is_serialized_header_chain v.(tlv_Vault_header) bytes ser_vault_rest1;

  ser_vault_rest1_len_ge_1 :
    (slice_len ser_vault_rest1 s< 1%usize) = false;

  ser_vault_slot_count_u8 : u8;
  ser_vault_idx_slot_count :
    slice_index_usize ser_vault_rest1 0%usize = Ok ser_vault_slot_count_u8;

  ser_vault_slot_count_usize : usize;
  ser_vault_cast_slot_count :
    scalar_cast U8 Usize ser_vault_slot_count_u8 = Ok ser_vault_slot_count_usize;

  ser_vault_slot_count_nat :
    usize_to_nat ser_vault_slot_count_usize = length v.(tlv_Vault_slots);

  ser_vault_rest2 : slice u8;
  ser_vault_extract_rest2 :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
      ser_vault_rest1 {| core_ops_range_RangeFrom_start := 1%usize |} =
    Ok ser_vault_rest2;

  ser_vault_needed_slot_len : usize;
  ser_vault_mul_needed_slot_len :
    core_num_Usize_saturating_mul ser_vault_slot_count_usize tlv_KEK_SLOT_HEADER_LEN =
      ser_vault_needed_slot_len;

  ser_vault_rest2_len_ge_slots :
    (slice_len ser_vault_rest2 s< ser_vault_needed_slot_len) = false;

  ser_vault_rest3 : slice u8;
  ser_vault_slots_chain :
    tlv_is_serialized_slots v.(tlv_Vault_slots) ser_vault_rest2 ser_vault_rest3;

  ser_vault_rest3_len_ge_2 :
    (slice_len ser_vault_rest3 s< 2%usize) = false;

  ser_vault_b0 : u8;
  ser_vault_b1 : u8;
  ser_vault_idx_b0 :
    slice_index_usize ser_vault_rest3 0%usize = Ok ser_vault_b0;
  ser_vault_idx_b1 :
    slice_index_usize ser_vault_rest3 1%usize = Ok ser_vault_b1;

  ser_vault_record_count_usize : usize;
  ser_vault_cast_record_count :
    scalar_cast U16 Usize
      (core_num_U16_from_be_bytes (mk_array 2%usize [ser_vault_b0; ser_vault_b1])) =
      Ok ser_vault_record_count_usize;

  ser_vault_record_count_nat :
    usize_to_nat ser_vault_record_count_usize = length v.(tlv_Vault_records);

  ser_vault_rest4 : slice u8;
  ser_vault_extract_rest4 :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
      ser_vault_rest3 {| core_ops_range_RangeFrom_start := 2%usize |} =
    Ok ser_vault_rest4;

  ser_vault_needed_record_len : usize;
  ser_vault_mul_needed_record_len :
    core_num_Usize_saturating_mul ser_vault_record_count_usize tlv_TLV_HEADER_LEN =
      ser_vault_needed_record_len;

  ser_vault_rest4_len_ge_records :
    (slice_len ser_vault_rest4 s< ser_vault_needed_record_len) = false;

  ser_vault_records_chain :
    tlv_is_serialized_records v.(tlv_Vault_records) ser_vault_rest4 slice_empty;
}.

(** [SPEC]
    最上位定理: 未知タグと既知タグが混在する Vault 構造全体に対する完全ラウンドトリップ定理。
    シリアライズ仕様を満たすバイト列 bytes に対し、tlv_deserialize を実行すると、
    元の Vault 構造体 v と空の残余スライスが完全に復元される。 *)
Theorem tlv_vault_roundtrip :
  forall (v : tlv_Vault_t) (bytes : slice u8),
    tlv_is_serialized_vault v bytes ->
    tlv_deserialize bytes = Ok (Core_result_Result_Ok (v, slice_empty)).
Proof.
  intros v bytes Hser.
  unfold tlv_deserialize.
  (* 1. ヘッダーのデシリアライズ *)
  rewrite (tlv_header_chain_roundtrip
             v.(tlv_Vault_header) bytes (ser_vault_rest1 v bytes Hser)
             (ser_vault_header v bytes Hser)).
  cbn [bind].
  (* 2. slot_count の読み取りと境界判定 *)
  rewrite (ser_vault_rest1_len_ge_1 v bytes Hser).
  rewrite (ser_vault_idx_slot_count v bytes Hser); cbn [bind].
  rewrite (ser_vault_cast_slot_count v bytes Hser); cbn [bind].
  rewrite (ser_vault_extract_rest2 v bytes Hser); cbn [bind].
  rewrite (ser_vault_mul_needed_slot_len v bytes Hser).
  rewrite (ser_vault_rest2_len_ge_slots v bytes Hser).
  (* 3. スロット列のデシリアライズ *)
  rewrite (ser_vault_slot_count_nat v bytes Hser).
  rewrite (tlv_slots_roundtrip
             v.(tlv_Vault_slots) (ser_vault_rest2 v bytes Hser) (ser_vault_rest3 v bytes Hser)
             (ser_vault_slots_chain v bytes Hser)).
  cbn [bind].
  (* 4. record_count の読み取りと境界判定 *)
  rewrite (ser_vault_rest3_len_ge_2 v bytes Hser).
  rewrite (ser_vault_idx_b0 v bytes Hser); cbn [bind].
  rewrite (ser_vault_idx_b1 v bytes Hser); cbn [bind].
  rewrite (ser_vault_cast_record_count v bytes Hser); cbn [bind].
  rewrite (ser_vault_extract_rest4 v bytes Hser); cbn [bind].
  rewrite (ser_vault_mul_needed_record_len v bytes Hser).
  rewrite (ser_vault_rest4_len_ge_records v bytes Hser).
  (* 5. レコード列のデシリアライズ *)
  rewrite (ser_vault_record_count_nat v bytes Hser).
  rewrite (tlv_records_roundtrip
             v.(tlv_Vault_records) (ser_vault_rest4 v bytes Hser) slice_empty
             (ser_vault_records_chain v bytes Hser)).
  cbn [bind].
  (* 6. Vault 構造体の再構成 *)
  rewrite (tlv_vault_eta v).
  reflexivity.
Qed.

(** ** 未知タグ構造保存 (UnknownTag Preservation) の検証。 *)

(** [SPEC]
    補題 12: 単一未知タグレコードに対する構造保存 (raw_bytes の不変性) 補題。
    旧バージョンクライアントが未知タグバイト列をパースして得た Unknown レコードは、
    元のバイナリから tag および raw_bytes が一切の変質・欠損なく復元され、
    かつ再シリアライズに必要な健全性条件 (最大長 255 バイト以下、tag <> TAG_ENTRY) を保持する。 *)
Lemma tlv_unknown_tag_structure_preservation :
  forall (tag : u8) (raw_bytes : alloc_vec_Vec u8) (bytes rest : slice u8)
         (Hser : tlv_is_serialized_unknown_chain tag raw_bytes bytes rest),
    tlv_deserialize_record bytes =
      Ok (Core_result_Result_Ok (Tlv_TlvRecord_Unknown tag raw_bytes, rest)) /\
    to_Z (alloc_vec_Vec_len raw_bytes) <= 255 /\
    (tag s= tlv_TAG_ENTRY) = false.
Proof.
  intros tag raw_bytes bytes rest Hser.
  split; [| split].
  - apply (tlv_record_chain_roundtrip (Tlv_TlvRecord_Unknown tag raw_bytes) bytes rest).
    apply Tlv_is_serialized_record_chain_Unknown.
    exact Hser.
  - exact (ser_unk_chain_valid_len tag raw_bytes bytes rest Hser).
  - exact (ser_unk_chain_tag_not_entry tag raw_bytes bytes rest Hser).
Qed.

(** [SPEC]
    補題 13: 最小未知タグレコードに対する構造保存 (raw_bytes の不変性) 補題。
    後続データのない単一未知タグバイト列をパースした場合、
    tag および raw_bytes が完全に復元され、空の残余スライスが返される。 *)
Lemma tlv_unknown_tag_structure_preservation_minimal :
  forall (tag : u8) (raw_bytes : alloc_vec_Vec u8) (bytes : slice u8)
         (Hser : tlv_is_serialized_unknown tag raw_bytes bytes),
    tlv_deserialize_record bytes =
      Ok (Core_result_Result_Ok (Tlv_TlvRecord_Unknown tag raw_bytes, slice_empty)) /\
    to_Z (alloc_vec_Vec_len raw_bytes) <= 255 /\
    (tag s= tlv_TAG_ENTRY) = false.
Proof.
  intros tag raw_bytes bytes Hser.
  apply (tlv_unknown_tag_structure_preservation tag raw_bytes bytes slice_empty Hser).
Qed.

(** [MODEL]
    レコード列から未知タグレコードの (tag, raw_bytes) のみを順序通り抽出する射影関数。 *)
Fixpoint extract_unknown_records (records : list tlv_TlvRecord_t) : list (u8 * alloc_vec_Vec u8) :=
  match records with
  | [] => []
  | Tlv_TlvRecord_Entry _ :: rs => extract_unknown_records rs
  | Tlv_TlvRecord_Unknown tag raw :: rs => (tag, raw) :: extract_unknown_records rs
  end.

(** [SPEC]
    補題 14: 混在レコード列に対する未知フィールド保存 (脱落・破損防止) 定理。
    新旧混在フォーマットのシリアライズバイト列を旧バージョンクライアントがパースした際、
    レコード列中に含まれるすべての未知フィールド (tag および raw_bytes) は、
    1 つも脱落せず、順序や内容が破損することなく完全に保存される。 *)
Lemma tlv_records_preserve_unknown_fields :
  forall (records : list tlv_TlvRecord_t) (bytes rest : slice u8),
    tlv_is_serialized_records records bytes rest ->
    forall (records' : list tlv_TlvRecord_t) (rest' : slice u8),
      tlv_deserialize_records (length records) bytes = Ok (Core_result_Result_Ok (records', rest')) ->
      extract_unknown_records records' = extract_unknown_records records.
Proof.
  intros records bytes rest Hser records' rest' Hdeser.
  pose proof (tlv_records_roundtrip records bytes rest Hser) as Hrt.
  rewrite Hrt in Hdeser.
  inv Hdeser.
  reflexivity.
Qed.

(** [SPEC]
    最上位定理: Vault 全体に対する未知フィールド構造保存定理。
    旧バージョンクライアントが未知タグを含む Vault バイト列をパースした際、
    復元された Vault 構造体内のすべての未知レコード (tag, raw_bytes) は、
    元の Vault 構造体と完全に一致し、一切の破損・脱落が生じない。 *)
Theorem tlv_vault_preserve_unknown_fields :
  forall (v : tlv_Vault_t) (bytes : slice u8),
    tlv_is_serialized_vault v bytes ->
    forall (v' : tlv_Vault_t) (rest' : slice u8),
      tlv_deserialize bytes = Ok (Core_result_Result_Ok (v', rest')) ->
      extract_unknown_records v'.(tlv_Vault_records) =
        extract_unknown_records v.(tlv_Vault_records).
Proof.
  intros v bytes Hser v' rest' Hdeser.
  pose proof (tlv_vault_roundtrip v bytes Hser) as Hrt.
  rewrite Hrt in Hdeser.
  inv Hdeser.
  reflexivity.
Qed.
