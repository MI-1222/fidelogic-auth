//! # TLVパーサー全域性(Totality)プロパティテストスイート。
//!
//! `proptest` を用いて以下の3カテゴリの入力を生成するカスタムストラテジを構築し、
//! 各テストケース 100,000 件(10万件)の走査で一切パニックしない全域性(Panic-Freedom)を実証する。
//!
//! 1. 任意の乱数バイト列(空・極小長・境界長・大サイズ)。
//! 2. 切り詰めヘッダーおよび構造境界切り詰めバイト列(`VaultHeader`, `TlvHeader`, `KekSlotEntry`, `Vault`)。
//! 3. 壊れたTLV長フィールド・スロット長フィールド・カウント不整合入力(`length` 超過/過小、`TAG_ENTRY` 短小長、過大 `slot_count` / `record_count`)。

use fidelogic_core::tlv::{
    AUTH_TAG_LEN, TAG_ENTRY, TLV_HEADER_LEN, TlvParseError, VAULT_HEADER_LEN, VAULT_MAGIC,
    VaultHeader, deserialize_header, parse_tlv_header, serialize_header, validate_tlv_bounds,
};
use proptest::prelude::*;

/// 10万件走査用の共通 `ProptestConfig` を構築する。
fn totality_proptest_config() -> ProptestConfig {
    ProptestConfig {
        cases: 100_000,
        failure_persistence: None,
        ..ProptestConfig::default()
    }
}

/// 任意の乱数バイト列を生成するカスタムストラテジ(極小長と中規模長を網羅)。
fn arb_random_bytes(max_len: usize) -> impl Strategy<Value = Vec<u8>> {
    let short_max = max_len.min(32);
    prop_oneof![
        2 => prop::collection::vec(any::<u8>(), 0..=short_max),
        3 => prop::collection::vec(any::<u8>(), 0..=max_len),
    ]
}

/// 切り詰められた `VaultHeader` バイト列(0..14バイト)を生成するカスタムストラテジ。
///
/// 有効マジック(`FVAU`)の途中・通過後の切り詰めと、不正マジックを含む任意切り詰めの双方を生成する。
fn arb_truncated_vault_header() -> impl Strategy<Value = Vec<u8>> {
    (
        any::<bool>(),
        0usize..VAULT_HEADER_LEN,
        any::<u8>(),
        any::<u8>(),
        any::<u64>(),
        prop::collection::vec(any::<u8>(), VAULT_HEADER_LEN),
    )
        .prop_map(
            |(use_valid_magic, trunc_len, version, suite_id, epoch_id, raw)| {
                if use_valid_magic {
                    let header = VaultHeader::new(version, suite_id, epoch_id);
                    serialize_header(&header)[..trunc_len].to_vec()
                } else {
                    raw[..trunc_len].to_vec()
                }
            },
        )
}

/// 切り詰めまたは壊れた長フィールドを持つ単体 TLV ヘッダー/レコードバイト列を生成するカスタムストラテジ。
fn arb_broken_tlv_bounds_bytes() -> impl Strategy<Value = Vec<u8>> {
    prop_oneof![
        // 0..2 バイトの切り詰め TLV ヘッダー。
        prop::collection::vec(any::<u8>(), 0..TLV_HEADER_LEN),
        // 宣言長 `declared_len` に対してペイロード長が不足・一致・余剰となる各種パターン。
        (
            prop_oneof![Just(TAG_ENTRY), any::<u8>()],
            prop_oneof![
                Just(0u8),
                0u8..(AUTH_TAG_LEN as u8),
                Just(AUTH_TAG_LEN as u8),
                Just(u8::MAX),
                any::<u8>(),
            ],
            0u8..4u8,
            prop::collection::vec(any::<u8>(), 0..=280),
        )
            .prop_map(|(tag, declared_len, mode, mut payload_pool)| {
                let target_len = match mode {
                    // 宣言長より不足(切り詰め・境界直前)。
                    0 => usize::from(declared_len).saturating_sub(1),
                    // 空またはごく短いペイロード。
                    1 => usize::from(declared_len).min(2),
                    // 宣言長とちょうど一致。
                    2 => usize::from(declared_len),
                    // 宣言長より余剰。
                    _ => usize::from(declared_len).saturating_add(7),
                };
                payload_pool.resize(target_len, 0x5au8);
                let mut out = Vec::with_capacity(TLV_HEADER_LEN + target_len);
                out.push(tag);
                out.push(declared_len);
                out.extend_from_slice(&payload_pool);
                out
            }),
    ]
}

/// ヘッダー・TLV基本境界パーサー向けの統合敵対的入力ストラテジ。
fn arb_header_and_tlv_adversarial_bytes() -> impl Strategy<Value = Vec<u8>> {
    prop_oneof![
        3 => arb_random_bytes(320),
        3 => arb_truncated_vault_header(),
        4 => arb_broken_tlv_bounds_bytes(),
    ]
}

proptest! {
    #![proptest_config(totality_proptest_config())]

    /// `parse_tlv_header`, `validate_tlv_bounds`, `deserialize_header` が
    /// 10万件の任意乱数・切り詰めヘッダー・壊れたTLV長に対してパニックしないことを検証。
    #[test]
    fn prop_header_and_tlv_bounds_totality_100k(bytes in arb_header_and_tlv_adversarial_bytes()) {
        let header_res = deserialize_header(&bytes);
        if bytes.len() < VAULT_HEADER_LEN {
            prop_assert_eq!(header_res.err(), Some(TlvParseError::UnexpectedEof));
        } else if bytes[..4] != VAULT_MAGIC {
            prop_assert_eq!(header_res.err(), Some(TlvParseError::InvalidMagic));
        } else {
            let Ok((header, rest)) = header_res else {
                return Err(TestCaseError::fail("有効マジックかつ十分長なら成功すべきである。"));
            };
            prop_assert_eq!(rest.len(), bytes.len() - VAULT_HEADER_LEN);
            prop_assert_eq!(&serialize_header(&header)[..], &bytes[..VAULT_HEADER_LEN]);
        }

        let tlv_hdr = parse_tlv_header(&bytes);
        let bounds_ok = validate_tlv_bounds(&bytes);
        match tlv_hdr {
            None => {
                prop_assert!(bytes.len() < TLV_HEADER_LEN);
                prop_assert!(!bounds_ok);
            }
            Some(hdr) => {
                let required = TLV_HEADER_LEN + usize::from(hdr.length);
                prop_assert_eq!(bounds_ok, bytes.len() >= required);
            }
        }
    }
}

#[cfg(feature = "alloc")]
mod alloc_totality_tests {
    use super::*;
    use fidelogic_core::tlv::{
        KEK_SLOT_HEADER_LEN, KekSlotEntry, TlvRecord, Vault, deserialize, deserialize_record,
        deserialize_slot_entry, serialize_slot_entry_into,
    };

    /// スロットエントリおよびTLVレコードの生成・破壊用サンプルデータを構築する。
    #[derive(Debug)]
    struct SampleVaultLayout {
        bytes: Vec<u8>,
        slot_len_offsets: Vec<usize>,
        record_count_offset: usize,
        record_len_offsets: Vec<usize>,
    }

    /// 任意のヘッダー・スロット仕様・レコード仕様から有効な `Vault` バイト列と各長さフィールドのオフセットを構築する。
    fn build_sample_vault_layout(
        version: u8,
        suite_id: u8,
        epoch_id: u64,
        raw_slots: &[(u8, u8, Vec<u8>)],
        raw_records: &[(bool, u8, Vec<u8>)],
    ) -> SampleVaultLayout {
        let header = VaultHeader::new(version, suite_id, epoch_id);
        let mut bytes = Vec::with_capacity(256);
        bytes.extend_from_slice(&serialize_header(&header));

        let slot_count = raw_slots.len().min(u8::MAX as usize);
        bytes.push(slot_count as u8);

        let mut slot_len_offsets = Vec::with_capacity(slot_count);
        for (slot_id, kdf_kind, payload) in raw_slots.iter().take(slot_count) {
            let entry_start = bytes.len();
            slot_len_offsets.push(entry_start + 2);
            let entry = KekSlotEntry::new(*slot_id, *kdf_kind, payload.clone())
                .expect("テスト生成サイズはu16::MAX以下である。");
            serialize_slot_entry_into(&entry, &mut bytes)
                .expect("有効なスロットエントリのシリアライズに成功する。");
        }

        let record_count_offset = bytes.len();
        let record_count = raw_records.len().min(u16::MAX as usize);
        bytes.extend_from_slice(&(record_count as u16).to_be_bytes());

        let mut record_len_offsets = Vec::with_capacity(record_count);
        for (is_known, raw_tag, payload) in raw_records.iter().take(record_count) {
            let rec_start = bytes.len();
            record_len_offsets.push(rec_start + 1);
            if *is_known {
                let ct_len = payload.len().min(255 - AUTH_TAG_LEN);
                bytes.push(TAG_ENTRY);
                bytes.push((ct_len + AUTH_TAG_LEN) as u8);
                bytes.extend_from_slice(&payload[..ct_len]);
                bytes.extend_from_slice(&[0xa5u8; AUTH_TAG_LEN]);
            } else {
                let tag = if *raw_tag == TAG_ENTRY { 2 } else { *raw_tag };
                let data_len = payload.len().min(255);
                bytes.push(tag);
                bytes.push(data_len as u8);
                bytes.extend_from_slice(&payload[..data_len]);
            }
        }

        SampleVaultLayout {
            bytes,
            slot_len_offsets,
            record_count_offset,
            record_len_offsets,
        }
    }

    /// 構造化された `SampleVaultLayout` を生成するカスタムストラテジ。
    fn arb_sample_vault_layout() -> impl Strategy<Value = SampleVaultLayout> {
        let slot_strat = (
            any::<u8>(),
            any::<u8>(),
            prop::collection::vec(any::<u8>(), 0..=112),
        );
        let rec_strat = (
            any::<bool>(),
            any::<u8>(),
            prop::collection::vec(any::<u8>(), 0..=48),
        );
        (
            any::<u8>(),
            any::<u8>(),
            any::<u64>(),
            prop::collection::vec(slot_strat, 0..=4),
            prop::collection::vec(rec_strat, 0..=6),
        )
            .prop_map(|(version, suite_id, epoch_id, slots, records)| {
                build_sample_vault_layout(version, suite_id, epoch_id, &slots, &records)
            })
    }

    /// `KekSlotEntry` 向けの壊れた長フィールド・切り詰め・乱数入力を生成するカスタムストラテジ。
    fn arb_adversarial_slot_entry_bytes() -> impl Strategy<Value = Vec<u8>> {
        prop_oneof![
            // 任意乱数バイト列。
            3 => arb_random_bytes(512),
            // 切り詰めスロットヘッダー(0..4バイト)。
            2 => prop::collection::vec(any::<u8>(), 0..KEK_SLOT_HEADER_LEN),
            // 壊れた16bit BE長さフィールド(u16::MAX, off-by-one, 過小/超過)。
            5 => (
                any::<u8>(),
                any::<u8>(),
                prop_oneof![
                    Just(0u16),
                    Just(1u16),
                    Just(100u16),
                    Just(104u16),
                    Just(256u16),
                    Just(u16::MAX),
                    any::<u16>(),
                ],
                0u8..4u8,
                prop::collection::vec(any::<u8>(), 0..=300),
            )
                .prop_map(|(slot_id, kdf_kind, declared_len, mode, payload)| {
                    let mut out = Vec::with_capacity(KEK_SLOT_HEADER_LEN + payload.len());
                    out.push(slot_id);
                    out.push(kdf_kind);
                    let effective_declared = match mode {
                        // 実ペイロード長 + 1 (off-by-one 超過)。
                        0 => u16::try_from(payload.len().saturating_add(1)).unwrap_or(u16::MAX),
                        _ => declared_len,
                    };
                    out.extend_from_slice(&effective_declared.to_be_bytes());
                    let keep_len = match mode {
                        // 宣言長より確実に短い。
                        1 => payload.len().min(usize::from(effective_declared).saturating_sub(1)),
                        // 宣言長に一致する長さまで切り詰め(ただし最大300)。
                        2 => payload.len().min(usize::from(effective_declared)),
                        _ => payload.len(),
                    };
                    out.extend_from_slice(&payload[..keep_len]);
                    out
                }),
        ]
    }

    /// `TlvRecord` 向けの壊れたTLV長フィールド・切り詰め・乱数入力を生成するカスタムストラテジ。
    fn arb_adversarial_record_bytes() -> impl Strategy<Value = Vec<u8>> {
        prop_oneof![
            // 任意乱数バイト列。
            3 => arb_random_bytes(512),
            // 切り詰めTLVヘッダー(0..2バイト)。
            2 => prop::collection::vec(any::<u8>(), 0..TLV_HEADER_LEN),
            // `TAG_ENTRY` に対して認証タグ長未満(0..16)の壊れた長フィールド。
            3 => (
                0u8..(AUTH_TAG_LEN as u8),
                prop::collection::vec(any::<u8>(), 0..=48),
            )
                .prop_map(|(bad_len, payload)| {
                    let mut out = Vec::with_capacity(TLV_HEADER_LEN + payload.len());
                    out.push(TAG_ENTRY);
                    out.push(bad_len);
                    out.extend_from_slice(&payload);
                    out
                }),
            // 任意タグ＋壊れた宣言長(過大・u8::MAX・off-by-one)。
            4 => arb_broken_tlv_bounds_bytes(),
        ]
    }

    /// 切り詰められた `Vault` バイト列を生成するカスタムストラテジ。
    fn arb_truncated_vault_bytes() -> impl Strategy<Value = Vec<u8>> {
        (
            arb_sample_vault_layout(),
            any::<prop::sample::Index>(),
            0u8..4u8,
        )
            .prop_map(|(layout, idx, mode)| {
                let len = layout.bytes.len();
                if len == 0 {
                    return Vec::new();
                }
                let cut = match mode {
                    // ヘッダー途中切り詰め(0..14バイト)。
                    0 => idx.index(VAULT_HEADER_LEN.min(len)),
                    // スロットテーブル付近切り詰め。
                    1 => {
                        let upper = (layout.record_count_offset + 2).min(len).max(1);
                        idx.index(upper)
                    }
                    // 空入力または1バイト切り詰め。
                    2 => 0,
                    // 全域から任意オフセットで切り詰め。
                    _ => idx.index(len),
                };
                layout.bytes[..cut].to_vec()
            })
    }

    /// 壊れたTLV長フィールドおよびカウント不整合を持つ `Vault` バイト列を生成するカスタムストラテジ。
    fn arb_corrupted_tlv_length_vault_bytes() -> impl Strategy<Value = Vec<u8>> {
        (
            arb_sample_vault_layout(),
            0u8..6u8,
            any::<prop::sample::Index>(),
            any::<u8>(),
            any::<u16>(),
            prop::collection::vec(any::<u8>(), 0..=64),
        )
            .prop_map(
                |(mut layout, mode, idx, bad_u8, bad_u16, extra)| match mode {
                    // モード0: 任意レコードのTLV長フィールドを破壊。
                    0 => {
                        if let Some(&pos) = (!layout.record_len_offsets.is_empty()).then(|| {
                            let i = idx.index(layout.record_len_offsets.len());
                            &layout.record_len_offsets[i]
                        }) {
                            let mutated = match bad_u8 % 4 {
                                0 => bad_u8 % (AUTH_TAG_LEN as u8),
                                1 => u8::MAX,
                                2 => layout.bytes[pos].wrapping_add(1),
                                _ => bad_u8,
                            };
                            layout.bytes[pos] = mutated;
                        } else {
                            // レコードが0件の場合は壊れたレコードを直接注入。
                            let rc_pos = layout.record_count_offset;
                            layout.bytes[rc_pos] = 0;
                            layout.bytes[rc_pos + 1] = 1;
                            layout.bytes.push(TAG_ENTRY);
                            layout.bytes.push(bad_u8 % (AUTH_TAG_LEN as u8));
                            layout.bytes.extend_from_slice(&extra);
                        }
                        layout.bytes
                    }
                    // モード1: 任意スロットの16bit BE長さフィールドを破壊。
                    1 => {
                        if let Some(&pos) = (!layout.slot_len_offsets.is_empty()).then(|| {
                            let i = idx.index(layout.slot_len_offsets.len());
                            &layout.slot_len_offsets[i]
                        }) {
                            let mutated_len: u16 = match bad_u8 % 4 {
                                0 => u16::MAX,
                                1 => u16::try_from(
                                    layout.bytes.len().saturating_sub(pos).saturating_add(1),
                                )
                                .unwrap_or(u16::MAX),
                                2 => 0,
                                _ => bad_u16,
                            };
                            let be = mutated_len.to_be_bytes();
                            layout.bytes[pos] = be[0];
                            layout.bytes[pos + 1] = be[1];
                        } else {
                            // スロット0件時は壊れたスロットを1件偽装。
                            layout.bytes[VAULT_HEADER_LEN] = 1;
                            layout.bytes.truncate(VAULT_HEADER_LEN + 1);
                            layout.bytes.extend_from_slice(&[0u8, 1u8]);
                            layout
                                .bytes
                                .extend_from_slice(&bad_u16.max(1).to_be_bytes());
                            layout.bytes.extend_from_slice(&extra);
                        }
                        layout.bytes
                    }
                    // モード2: `slot_count` 誇張(Allocation DoS・カウント不整合耐性)。
                    2 => {
                        layout.bytes[VAULT_HEADER_LEN] = bad_u8.max(1);
                        if bad_u8 & 1 == 0 {
                            layout.bytes[VAULT_HEADER_LEN] = u8::MAX;
                        }
                        layout.bytes
                    }
                    // モード3: `record_count` 誇張(u16::MAX 爆弾・カウント不整合耐性)。
                    3 => {
                        let rc_pos = layout.record_count_offset;
                        let count = if bad_u8 & 1 == 0 {
                            u16::MAX
                        } else {
                            bad_u16.max(1)
                        };
                        let be = count.to_be_bytes();
                        layout.bytes[rc_pos] = be[0];
                        layout.bytes[rc_pos + 1] = be[1];
                        layout.bytes
                    }
                    // モード4: 有効ヘッダー直後に `TAG_ENTRY` 短小長レコードを配置して InvalidLength を誘発。
                    4 => {
                        let mut out = layout.bytes[..VAULT_HEADER_LEN].to_vec();
                        out.push(0); // slot_count = 0。
                        out.extend_from_slice(&1u16.to_be_bytes()); // record_count = 1。
                        out.push(TAG_ENTRY);
                        let short_len = bad_u8 % (AUTH_TAG_LEN as u8);
                        out.push(short_len);
                        out.extend_from_slice(&vec![0x7cu8; usize::from(short_len)]);
                        out.extend_from_slice(&extra);
                        out
                    }
                    // モード5: 有効構造の任意バイト改変または末尾ゴミバイト付加。
                    _ => {
                        if !layout.bytes.is_empty() {
                            let target = idx.index(layout.bytes.len());
                            layout.bytes[target] ^= bad_u8.max(1);
                        }
                        layout.bytes.extend_from_slice(&extra);
                        layout.bytes
                    }
                },
            )
    }

    /// `Vault` 全体デシリアライザー向けの統合敵対的入力ストラテジ。
    ///
    /// 任意乱数バイト列・切り詰めヘッダー/Vault・壊れたTLV長フィールドをバランスよく生成する。
    fn arb_adversarial_vault_bytes() -> impl Strategy<Value = Vec<u8>> {
        prop_oneof![
            3 => arb_random_bytes(1024),
            2 => arb_truncated_vault_header(),
            2 => arb_truncated_vault_bytes(),
            3 => arb_corrupted_tlv_length_vault_bytes(),
        ]
    }

    /// `Vault` デシリアライズ結果のエラーバリアントが既知の6種であることを確認するヘルパー。
    fn is_valid_parse_error(err: TlvParseError) -> bool {
        matches!(
            err,
            TlvParseError::UnexpectedEof
                | TlvParseError::InvalidMagic
                | TlvParseError::UnsupportedVersion
                | TlvParseError::UnsupportedSuite
                | TlvParseError::InvalidLength
                | TlvParseError::InvalidFormat
        )
    }

    proptest! {
        #![proptest_config(totality_proptest_config())]

        /// `deserialize_slot_entry` および `deserialize_record` が 10万件の
        /// 乱数・切り詰め・壊れた長フィールド入力に対して一切パニックしないことを検証。
        #[test]
        fn prop_slot_entry_and_record_totality_100k(
            slot_bytes in arb_adversarial_slot_entry_bytes(),
            record_bytes in arb_adversarial_record_bytes(),
        ) {
            match deserialize_slot_entry(&slot_bytes) {
                Ok((entry, rest)) => {
                    prop_assert!(rest.len() <= slot_bytes.len());
                    prop_assert_eq!(entry.wrapped_dek().len(), usize::from(entry.wrapped_dek_len()));
                    prop_assert_eq!(
                        KEK_SLOT_HEADER_LEN + entry.wrapped_dek().len() + rest.len(),
                        slot_bytes.len()
                    );
                }
                Err(err) => {
                    prop_assert!(is_valid_parse_error(err));
                }
            }

            match deserialize_record(&record_bytes) {
                Ok((record, rest)) => {
                    prop_assert!(rest.len() <= record_bytes.len());
                    match &record {
                        TlvRecord::Entry(payload) => {
                            let expected = TLV_HEADER_LEN + payload.ciphertext.len() + AUTH_TAG_LEN;
                            prop_assert_eq!(expected + rest.len(), record_bytes.len());
                        }
                        TlvRecord::Unknown { tag, raw_bytes } => {
                            prop_assert_ne!(*tag, TAG_ENTRY);
                            let expected = TLV_HEADER_LEN + raw_bytes.len();
                            prop_assert_eq!(expected + rest.len(), record_bytes.len());
                        }
                    }
                }
                Err(err) => {
                    prop_assert!(is_valid_parse_error(err));
                }
            }
        }

        /// `deserialize` (`Vault` 全体パーサー) が 10万件の任意乱数バイト列・切り詰めヘッダー・
        /// 壊れたTLV長フィールドおよびカウント不整合入力に対して一切パニックしない全域性を実証。
        #[test]
        fn prop_deserialize_vault_totality_100k(bytes in arb_adversarial_vault_bytes()) {
            match deserialize(&bytes) {
                Ok((vault, rest)) => {
                    let _vault_ref: &Vault = &vault;
                    prop_assert!(rest.len() <= bytes.len());
                    prop_assert_eq!(vault.header.magic, VAULT_MAGIC);
                    prop_assert!(vault.slots.len() <= usize::from(u8::MAX));
                    prop_assert!(vault.records.len() <= usize::from(u16::MAX));
                    for slot in &vault.slots {
                        prop_assert_eq!(slot.wrapped_dek().len(), usize::from(slot.wrapped_dek_len()));
                    }
                    for record in &vault.records {
                        if let TlvRecord::Unknown { tag, .. } = record {
                            prop_assert_ne!(*tag, TAG_ENTRY);
                        }
                    }
                }
                Err(err) => {
                    prop_assert!(is_valid_parse_error(err));
                }
            }
        }
    }
}

#[cfg(feature = "profile-vault")]
mod slot_payload_totality_tests {
    use super::*;
    use fidelogic_core::tlv::deserialize;
    use fidelogic_core::{
        Argon2idSlotPayload, PrfSlotPayload, RecoverySlotPayload, SLOT0_WRAPPED_DEK_LEN,
        SLOT1_WRAPPED_DEK_LEN, find_slot_entry, inspect_kek_slots,
    };

    /// 固定長スロットペイロード(100B / 104B)およびVaultスロット結合境界向けの敵対的入力ストラテジ。
    fn arb_slot_payload_bytes() -> impl Strategy<Value = Vec<u8>> {
        prop_oneof![
            3 => arb_random_bytes(256),
            2 => prop::collection::vec(any::<u8>(), 0..SLOT0_WRAPPED_DEK_LEN),
            3 => prop::collection::vec(any::<u8>(), SLOT0_WRAPPED_DEK_LEN..=SLOT0_WRAPPED_DEK_LEN),
            2 => prop::collection::vec(any::<u8>(), SLOT1_WRAPPED_DEK_LEN..=SLOT1_WRAPPED_DEK_LEN),
        ]
    }

    proptest! {
        #![proptest_config(totality_proptest_config())]

        /// スロットペイロードデコーダ(`from_bytes`)および `inspect_kek_slots` 連携が
        /// 10万件の任意・切り詰め・境界バイト列でパニックしないことを検証。
        #[test]
        fn prop_slot_payload_and_inspect_totality_100k(
            payload_bytes in arb_slot_payload_bytes(),
            vault_bytes in arb_random_bytes(256),
        ) {
            let _ = Argon2idSlotPayload::from_bytes(&payload_bytes);
            let _ = PrfSlotPayload::from_bytes(&payload_bytes);
            let _ = RecoverySlotPayload::from_bytes(&payload_bytes);

            if let Ok((vault, _)) = deserialize(&vault_bytes) {
                let _slots = inspect_kek_slots(&vault.slots);
                let _ = find_slot_entry(&vault.slots, 0);
                let _ = find_slot_entry(&vault.slots, 1);
                let _ = find_slot_entry(&vault.slots, 2);
            }
        }
    }
}
