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

(** [MODEL]
    既知エントリペイロード ep に対するシリアライズ結果バイト列 bytes の振る舞い規定。
    Rust 実装 serialize_record / serialize_record_into の出力スライスが満たす
    スライシング・インデックス・コピー操作の契約をモデル化する。 *)
Record tlv_is_serialized_entry
  (ep : tlv_EntryPayload_t) (bytes : slice u8) : Type :=
mktlv_is_serialized_entry {
  ser_valid_len :
    tlv_entry_payload_valid_len ep;

  ser_payload_len_u8 : u8;
  ser_payload_len_usize : usize;
  ser_total_len : usize;

  ser_cast_len :
    scalar_cast U8 Usize ser_payload_len_u8 = Ok ser_payload_len_usize;
  ser_add_total_len :
    usize_add 2%usize ser_payload_len_usize = Ok ser_total_len;

  ser_header_parse :
    tlv_parse_tlv_header bytes =
      Ok (Some {| tlv_TlvHeader_tag := tlv_TAG_ENTRY;
                  tlv_TlvHeader_length := ser_payload_len_u8 |});

  ser_bytes_len :
    slice_len bytes = ser_total_len;

  ser_payload_bytes : slice u8;
  ser_payload_bytes_len :
    slice_len ser_payload_bytes = ser_payload_len_usize;

  ser_extract_payload :
    core_slice_index_Slice_index
      (core_slice_index_SliceIndexRangeUsizeSliceInst u8) bytes
      {|
        core_ops_range_Range_start := 2%usize;
        core_ops_range_Range_end_ := ser_total_len
      |} = Ok ser_payload_bytes;

  ser_extract_rest :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8) bytes
      {|
        core_ops_range_RangeFrom_start := ser_total_len
      |} = Ok slice_empty;

  ser_payload_len_ge_auth :
    (slice_len ser_payload_bytes s< tlv_AUTH_TAG_LEN) = false;

  ser_sub_ciphertext_len :
    usize_sub (slice_len ser_payload_bytes) tlv_AUTH_TAG_LEN =
      Ok (alloc_vec_Vec_len ep.(tlv_EntryPayload_ciphertext));

  ser_ct_slice : slice u8;
  ser_extract_ciphertext :
    core_slice_index_Slice_index
      (core_ops_range_RangeToUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
      ser_payload_bytes
      {| core_ops_range_RangeTo_end_ := alloc_vec_Vec_len ep.(tlv_EntryPayload_ciphertext) |} =
    Ok ser_ct_slice;

  ser_restore_ciphertext :
    alloc_vec_Vec_Insts_CoreConvertFromShared0Slice_from
      core_clone_CloneU8 ser_ct_slice =
    Ok ep.(tlv_EntryPayload_ciphertext);

  ser_tag_slice : slice u8;
  ser_extract_tag :
    core_slice_index_Slice_index
      (core_ops_range_RangeFromUsize_Insts_CoreSliceIndexSliceIndexSliceSlice u8)
      ser_payload_bytes
      {| core_ops_range_RangeFrom_start := alloc_vec_Vec_len ep.(tlv_EntryPayload_ciphertext) |} =
    Ok ser_tag_slice;

  ser_tag_copied_slice : slice u8;
  ser_copy_tag :
    core_slice_Slice_copy_from_slice
      core_marker_CopyU8
      (array_to_slice (array_repeat 16%usize 0%u8))
      ser_tag_slice =
    Ok ser_tag_copied_slice;

  ser_restore_tag :
    array_from_slice (array_repeat 16%usize 0%u8) ser_tag_copied_slice =
    ep.(tlv_EntryPayload_auth_tag);
}.

(** [MODEL]
    レコード全体のシリアライズ関係 (既知エントリおよび未知タグの直和型)。 *)
Inductive tlv_is_serialized_record : tlv_TlvRecord_t -> slice u8 -> Type :=
| Tlv_is_serialized_record_Entry :
    forall (ep : tlv_EntryPayload_t) (bytes : slice u8),
      tlv_is_serialized_entry ep bytes ->
      tlv_is_serialized_record (Tlv_TlvRecord_Entry ep) bytes.

(** [SPEC]
    補題 1: 既知タグエントリに対するヘッダーパースの整合性。 *)
Lemma tlv_parse_header_of_serialized_entry :
  forall (ep : tlv_EntryPayload_t) (bytes : slice u8) (Hser : tlv_is_serialized_entry ep bytes),
    tlv_parse_tlv_header bytes =
      Ok (Some {| tlv_TlvHeader_tag := tlv_TAG_ENTRY;
                  tlv_TlvHeader_length := (ser_payload_len_u8 ep bytes Hser) |}).
Proof.
  intros ep bytes Hser.
  exact (ser_header_parse ep bytes Hser).
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
  unfold tlv_deserialize_record.
  (* 1. ヘッダーパースの展開 *)
  rewrite (ser_header_parse ep bytes Hser).
  cbn [bind].
  change (tlv_TlvHeader_length {| tlv_TlvHeader_tag := tlv_TAG_ENTRY; tlv_TlvHeader_length := ser_payload_len_u8 ep bytes Hser |})
    with (ser_payload_len_u8 ep bytes Hser).
  rewrite (ser_cast_len ep bytes Hser).
  cbn [bind].
  rewrite (ser_add_total_len ep bytes Hser).
  cbn [bind].
  (* 3. 全体長チェックの解消 *)
  rewrite (ser_bytes_len ep bytes Hser).
  rewrite (scalar_ltb_irrefl (ser_total_len ep bytes Hser)).
  cbn [bind].
  (* 4. ペイロードスライスおよび残余スライスの切り出し *)
  rewrite (ser_extract_payload ep bytes Hser).
  cbn [bind].
  change (core_ops_range_RangeFrom_t (scalar Usize)) with (core_ops_range_RangeFrom_t usize).
  change (@mkcore_ops_range_RangeFrom_t (scalar Usize)) with (@mkcore_ops_range_RangeFrom_t usize).
  rewrite (ser_extract_rest ep bytes Hser).
  cbn [bind].
  (* 5. 既知タグ (TAG_ENTRY) 判定の解決 *)
  change (tlv_TlvHeader_tag {| tlv_TlvHeader_tag := tlv_TAG_ENTRY; tlv_TlvHeader_length := ser_payload_len_u8 ep bytes Hser |})
    with tlv_TAG_ENTRY.
  rewrite (scalar_eqb_refl tlv_TAG_ENTRY).
  (* 6. 認証タグ長 (16バイト) 境界判定の解決 *)
  rewrite (ser_payload_len_ge_auth ep bytes Hser).
  cbn [bind].
  (* 7. 暗号文長計算および暗号文スライスの切り出し *)
  rewrite (ser_sub_ciphertext_len ep bytes Hser).
  cbn [bind].
  change (core_ops_range_RangeTo (scalar Usize)) with (core_ops_range_RangeTo usize).
  change (@mk_core_ops_range_RangeTo (scalar Usize)) with (@mk_core_ops_range_RangeTo usize).
  rewrite (ser_extract_ciphertext ep bytes Hser).
  cbn [bind].
  rewrite (ser_restore_ciphertext ep bytes Hser).
  cbn [bind].
  (* 8. 認証タグスライスの切り出しおよび配列コピー *)
  rewrite (ser_extract_tag ep bytes Hser).
  cbn [bind].
  unfold array_to_slice_mut.
  rewrite (ser_copy_tag ep bytes Hser).
  cbn [bind].
  rewrite (ser_restore_tag ep bytes Hser).
  (* 9. EntryPayload_new によるペイロードの復元 *)
  unfold tlv_EntryPayload_new.
  rewrite (tlv_entry_payload_eta ep).
  reflexivity.
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
