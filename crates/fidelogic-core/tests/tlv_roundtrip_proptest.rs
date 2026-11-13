//! # TLVラウンドトリップ・未知タグ不変性プロパティテストスイート。
//!
//! `proofs/Theories/TlvRoundtrip.v` で形式証明された以下の定理群を、
//! ランダム生成 Vault データに対するプロパティテストとして検証する。
//!
//! 1. ヘッダー可逆性 (`tlv_header_roundtrip_sound` / `tlv_header_chain_roundtrip`)。
//! 2. 単一スロット・既知/未知レコード連鎖可逆性 (`tlv_slot_roundtrip_sound` / `tlv_record_chain_roundtrip`)。
//! 3. 既知・未知タグ混在 Vault 全体の完全可逆性およびワイヤー表現整合性 (`tlv_vault_roundtrip_sound`)。
//! 4. 未知タグレコードの脱落・並べ替え・改変防止およびバイト不変性、
//!    (`tlv_unknown_tag_structure_preservation` / `tlv_records_preserve_unknown_fields` /
//!    `tlv_vault_preserve_unknown_fields`)。
//! 5. (`profile-vault`) AEAD 暗号化エントリと未知タグが混在する Vault の復号・更新を跨ぐ不変性。

use fidelogic_core::tlv::{
    VAULT_HEADER_LEN, VAULT_MAGIC, VaultHeader, deserialize_header, serialize_header,
};
use proptest::prelude::*;

/// ラウンドトリップ検証用の `ProptestConfig` を構築する。
fn roundtrip_proptest_config(cases: u32) -> ProptestConfig {
    ProptestConfig {
        cases,
        failure_persistence: None,
        ..ProptestConfig::default()
    }
}

/// テスト用のデバッグ出力可能な `VaultHeader` 仕様型。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct HeaderSpec {
    version: u8,
    suite_id: u8,
    epoch_id: u64,
}

impl HeaderSpec {
    fn to_header(self) -> VaultHeader {
        VaultHeader::new(self.version, self.suite_id, self.epoch_id)
    }
}

/// 任意の `HeaderSpec` を生成するストラテジ(境界世代値を含む)。
fn arb_header_spec() -> impl Strategy<Value = HeaderSpec> {
    let epoch_strat = prop_oneof![
        1 => Just(0u64),
        1 => Just(1u64),
        1 => Just(u64::MAX - 1),
        1 => Just(u64::MAX),
        4 => any::<u64>(),
    ];
    (any::<u8>(), any::<u8>(), epoch_strat).prop_map(|(version, suite_id, epoch_id)| HeaderSpec {
        version,
        suite_id,
        epoch_id,
    })
}

/// 任意の残余バイト列を生成するストラテジ(空スライスおよび擬似ヘッダー列を含む)。
fn arb_trailing_bytes() -> impl Strategy<Value = Vec<u8>> {
    prop_oneof![
        2 => Just(Vec::new()),
        1 => Just(VAULT_MAGIC.to_vec()),
        3 => prop::collection::vec(any::<u8>(), 1..=64),
    ]
}

proptest! {
    #![proptest_config(roundtrip_proptest_config(4096))]

    /// `tlv_header_roundtrip_sound` / `tlv_header_chain_roundtrip` に対応し、
    /// 任意の `VaultHeader` と後続残余バイト列の往復可逆性を検証する。
    #[test]
    fn prop_header_roundtrip_and_trailing_slice(
        header_spec in arb_header_spec(),
        trailing in arb_trailing_bytes(),
    ) {
        let header = header_spec.to_header();
        let serialized = serialize_header(&header);
        prop_assert_eq!(serialized.len(), VAULT_HEADER_LEN);
        prop_assert_eq!(&serialized[..4], &VAULT_MAGIC);
        prop_assert_eq!(serialized, header.associated_data());

        let (restored_only, rest_only) = deserialize_header(&serialized)
            .map_err(|e| TestCaseError::fail(format!("ヘッダー単体復元に失敗: {e:?}")))?;
        prop_assert_eq!(restored_only.magic, header.magic);
        prop_assert_eq!(restored_only.version, header.version);
        prop_assert_eq!(restored_only.suite_id, header.suite_id);
        prop_assert_eq!(restored_only.epoch_id, header.epoch_id);
        prop_assert!(rest_only.is_empty());

        let mut combined = Vec::with_capacity(VAULT_HEADER_LEN + trailing.len());
        combined.extend_from_slice(&serialized);
        combined.extend_from_slice(&trailing);

        let (restored_chain, rest_chain) = deserialize_header(&combined)
            .map_err(|e| TestCaseError::fail(format!("残余付きヘッダー復元に失敗: {e:?}")))?;
        prop_assert!(restored_chain == header);
        prop_assert_eq!(rest_chain, trailing.as_slice());
    }
}

#[cfg(feature = "alloc")]
mod alloc_roundtrip_tests {
    use super::*;
    use fidelogic_core::tlv::{
        AUTH_TAG_LEN, EntryPayload, KEK_SLOT_HEADER_LEN, KekSlotEntry, TAG_ENTRY, TLV_HEADER_LEN,
        TlvParseError, TlvRecord, Vault, deserialize, deserialize_record, deserialize_slot_entry,
        is_known_tag, record_serialized_len, serialize, serialize_record, serialize_record_into,
        serialize_slot_entry, serialize_slot_entry_into, slot_serialized_len,
    };

    /// テスト用のデバッグ出力可能な `KekSlotEntry` 仕様型。
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct SlotSpec {
        slot_id: u8,
        kdf_kind: u8,
        wrapped_dek: Vec<u8>,
    }

    impl SlotSpec {
        fn to_slot(&self) -> KekSlotEntry {
            KekSlotEntry::new(self.slot_id, self.kdf_kind, self.wrapped_dek.clone())
                .expect("SlotSpecのwrapped_dek長はu16::MAX以下である。")
        }
    }

    /// テスト用のデバッグ出力可能な `EntryPayload` 仕様型。
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct EntrySpec {
        ciphertext: Vec<u8>,
        auth_tag: [u8; AUTH_TAG_LEN],
    }

    impl EntrySpec {
        fn to_payload(&self) -> EntryPayload {
            EntryPayload::new(self.ciphertext.clone(), self.auth_tag)
        }
    }

    /// テスト用のデバッグ出力可能な `TlvRecord` 仕様型。
    #[derive(Debug, Clone, PartialEq, Eq)]
    enum RecordSpec {
        Entry(EntrySpec),
        Unknown { tag: u8, raw_bytes: Vec<u8> },
    }

    impl RecordSpec {
        fn to_record(&self) -> TlvRecord {
            match self {
                Self::Entry(ep) => TlvRecord::Entry(ep.to_payload()),
                Self::Unknown { tag, raw_bytes } => TlvRecord::new_unknown(*tag, raw_bytes.clone())
                    .expect("RecordSpec::UnknownのtagはTAG_ENTRY以外である。"),
            }
        }
    }

    /// テスト用のデバッグ出力可能な `Vault` 仕様型。
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct VaultSpec {
        header: HeaderSpec,
        slots: Vec<SlotSpec>,
        records: Vec<RecordSpec>,
    }

    impl VaultSpec {
        fn to_vault(&self) -> Vault {
            Vault::new(
                self.header.to_header(),
                self.slots.iter().map(SlotSpec::to_slot).collect(),
                self.records.iter().map(RecordSpec::to_record).collect(),
            )
        }
    }

    /// `TlvRoundtrip.v` の `extract_unknown_records` に対応し、
    /// レコード列から未知タグレコードの `(tag, raw_bytes)` のみを出現順に抽出する。
    fn extract_unknown_records(records: &[TlvRecord]) -> Vec<(u8, Vec<u8>)> {
        records
            .iter()
            .filter_map(|rec| match rec {
                TlvRecord::Entry(_) => None,
                TlvRecord::Unknown { tag, raw_bytes } => Some((*tag, raw_bytes.clone())),
            })
            .collect()
    }

    /// `KekSlotEntry` の構造等価性を検証するヘルパー。
    fn assert_slot_eq(actual: &KekSlotEntry, expected: &KekSlotEntry) -> Result<(), TestCaseError> {
        prop_assert_eq!(actual.slot_id(), expected.slot_id());
        prop_assert_eq!(actual.kdf_kind(), expected.kdf_kind());
        prop_assert_eq!(actual.wrapped_dek(), expected.wrapped_dek());
        Ok(())
    }

    /// `TlvRecord` の構造等価性を検証するヘルパー。
    fn assert_record_eq(actual: &TlvRecord, expected: &TlvRecord) -> Result<(), TestCaseError> {
        match (actual, expected) {
            (TlvRecord::Entry(a), TlvRecord::Entry(e)) => {
                prop_assert_eq!(a.ciphertext.as_slice(), e.ciphertext.as_slice());
                prop_assert_eq!(a.auth_tag, e.auth_tag);
                Ok(())
            }
            (
                TlvRecord::Unknown {
                    tag: a_tag,
                    raw_bytes: a_raw,
                },
                TlvRecord::Unknown {
                    tag: e_tag,
                    raw_bytes: e_raw,
                },
            ) => {
                prop_assert_eq!(*a_tag, *e_tag);
                prop_assert_eq!(a_raw.as_slice(), e_raw.as_slice());
                Ok(())
            }
            _ => Err(TestCaseError::fail(format!(
                "TlvRecordバリアント不一致: actual_tag={}, expected_tag={}",
                actual.tag(),
                expected.tag()
            ))),
        }
    }

    /// `Vault` 全体の構造等価性を検証するヘルパー。
    fn assert_vault_eq(actual: &Vault, expected: &Vault) -> Result<(), TestCaseError> {
        prop_assert_eq!(actual.header.magic, expected.header.magic);
        prop_assert_eq!(actual.header.version, expected.header.version);
        prop_assert_eq!(actual.header.suite_id, expected.header.suite_id);
        prop_assert_eq!(actual.header.epoch_id, expected.header.epoch_id);
        prop_assert_eq!(actual.slots.len(), expected.slots.len());
        for (a_slot, e_slot) in actual.slots.iter().zip(expected.slots.iter()) {
            assert_slot_eq(a_slot, e_slot)?;
        }
        prop_assert_eq!(actual.records.len(), expected.records.len());
        for (a_rec, e_rec) in actual.records.iter().zip(expected.records.iter()) {
            assert_record_eq(a_rec, e_rec)?;
        }
        prop_assert!(actual == expected);
        Ok(())
    }

    /// 既知タグ (`TAG_ENTRY`) 以外の任意の未知タグを生成するストラテジ。
    fn arb_unknown_tag() -> impl Strategy<Value = u8> {
        prop_oneof![
            1 => Just(0u8),
            1 => Just(2u8),
            1 => Just(u8::MAX),
            5 => (0u8..=u8::MAX).prop_filter("TAG_ENTRYは除外。", |&tag| tag != TAG_ENTRY),
        ]
    }

    /// 未知タグレコード用の生バイト列を生成するストラテジ(境界長・擬似TLV列を含む)。
    fn arb_unknown_raw_bytes() -> impl Strategy<Value = Vec<u8>> {
        prop_oneof![
            1 => Just(Vec::new()),
            1 => Just(vec![TAG_ENTRY, 0x00, TAG_ENTRY, 0xff]),
            1 => Just(VAULT_MAGIC.to_vec()),
            1 => prop::collection::vec(Just(0xffu8), 255..=255),
            4 => prop::collection::vec(any::<u8>(), 1..=255),
        ]
    }

    /// 未知タグレコード仕様を生成するストラテジ。
    fn arb_unknown_record_spec() -> impl Strategy<Value = RecordSpec> {
        (arb_unknown_tag(), arb_unknown_raw_bytes())
            .prop_map(|(tag, raw_bytes)| RecordSpec::Unknown { tag, raw_bytes })
    }

    /// 既知エントリペイロード仕様を生成するストラテジ(境界長 0 / 239 を含む)。
    fn arb_entry_spec() -> impl Strategy<Value = EntrySpec> {
        let max_ct_len = (u8::MAX as usize) - AUTH_TAG_LEN;
        let ct_strat = prop_oneof![
            1 => Just(Vec::new()),
            1 => prop::collection::vec(any::<u8>(), max_ct_len..=max_ct_len),
            4 => prop::collection::vec(any::<u8>(), 1..=max_ct_len),
        ];
        (ct_strat, any::<[u8; AUTH_TAG_LEN]>()).prop_map(|(ciphertext, auth_tag)| EntrySpec {
            ciphertext,
            auth_tag,
        })
    }

    /// 既知または未知の単一 `RecordSpec` を生成するストラテジ。
    fn arb_record_spec() -> impl Strategy<Value = RecordSpec> {
        prop_oneof![
            1 => arb_entry_spec().prop_map(RecordSpec::Entry),
            1 => arb_unknown_record_spec(),
        ]
    }

    /// 空・既知のみ・未知のみ・混在順序を網羅するレコード列ストラテジ。
    fn arb_mixed_record_specs() -> impl Strategy<Value = Vec<RecordSpec>> {
        prop_oneof![
            1 => Just(Vec::new()),
            2 => prop::collection::vec(arb_entry_spec().prop_map(RecordSpec::Entry), 1..=16),
            2 => prop::collection::vec(arb_unknown_record_spec(), 1..=16),
            5 => prop::collection::vec(arb_record_spec(), 1..=48),
        ]
    }

    /// 任意の `SlotSpec` を生成するストラテジ(Slot 0/1/2 の実長 100/104B を含む)。
    fn arb_slot_spec() -> impl Strategy<Value = SlotSpec> {
        let dek_strat = prop_oneof![
            1 => Just(Vec::new()),
            1 => prop::collection::vec(any::<u8>(), 100..=100),
            1 => prop::collection::vec(any::<u8>(), 104..=104),
            1 => prop::collection::vec(any::<u8>(), 255..=256),
            3 => prop::collection::vec(any::<u8>(), 1..=512),
        ];
        (any::<u8>(), any::<u8>(), dek_strat).prop_map(|(slot_id, kdf_kind, wrapped_dek)| {
            SlotSpec {
                slot_id,
                kdf_kind,
                wrapped_dek,
            }
        })
    }

    /// ランダムな既知・未知タグ混在 `VaultSpec` を生成するストラテジ。
    fn arb_mixed_vault_spec() -> impl Strategy<Value = VaultSpec> {
        (
            arb_header_spec(),
            prop::collection::vec(arb_slot_spec(), 0..=12),
            arb_mixed_record_specs(),
        )
            .prop_map(|(header, slots, records)| VaultSpec {
                header,
                slots,
                records,
            })
    }

    proptest! {
        #![proptest_config(roundtrip_proptest_config(4096))]

        /// `tlv_slot_roundtrip_sound` / `tlv_record_roundtrip_entry_sound` /
        /// `tlv_record_roundtrip_unknown_sound` / `tlv_record_chain_roundtrip` の検証。
        #[test]
        fn prop_slot_and_record_chain_roundtrip(
            slot_spec in arb_slot_spec(),
            record_spec in arb_record_spec(),
            trailing in arb_trailing_bytes(),
        ) {
            let slot = slot_spec.to_slot();
            let record = record_spec.to_record();

            // スロット単体のシリアライズ契約と残余付きデシリアライズ可逆性。
            let slot_bytes = serialize_slot_entry(&slot)
                .map_err(|e| TestCaseError::fail(format!("スロットシリアライズ失敗: {e:?}")))?;
            let expected_slot_len = slot_serialized_len(&slot)
                .map_err(|e| TestCaseError::fail(format!("スロット長計算失敗: {e:?}")))?;
            prop_assert_eq!(slot_bytes.len(), expected_slot_len);
            prop_assert_eq!(slot_bytes.len(), KEK_SLOT_HEADER_LEN + slot.wrapped_dek().len());

            let mut slot_into_buf = vec![0xaa, 0xbb];
            serialize_slot_entry_into(&slot, &mut slot_into_buf)
                .map_err(|e| TestCaseError::fail(format!("スロット追記失敗: {e:?}")))?;
            prop_assert_eq!(&slot_into_buf[2..], slot_bytes.as_slice());

            let mut slot_chain = slot_bytes;
            slot_chain.extend_from_slice(&trailing);
            let (restored_slot, slot_rest) = deserialize_slot_entry(&slot_chain)
                .map_err(|e| TestCaseError::fail(format!("スロット復元失敗: {e:?}")))?;
            assert_slot_eq(&restored_slot, &slot)?;
            prop_assert_eq!(slot_rest, trailing.as_slice());

            // レコード単体のシリアライズ契約と残余付きデシリアライズ可逆性。
            let rec_bytes = serialize_record(&record)
                .map_err(|e| TestCaseError::fail(format!("レコードシリアライズ失敗: {e:?}")))?;
            let expected_rec_len = record_serialized_len(&record)
                .map_err(|e| TestCaseError::fail(format!("レコード長計算失敗: {e:?}")))?;
            prop_assert_eq!(rec_bytes.len(), expected_rec_len);

            let mut rec_into_buf = vec![0x11];
            serialize_record_into(&record, &mut rec_into_buf)
                .map_err(|e| TestCaseError::fail(format!("レコード追記失敗: {e:?}")))?;
            prop_assert_eq!(&rec_into_buf[1..], rec_bytes.as_slice());

            match &record {
                TlvRecord::Entry(ep) => {
                    prop_assert!(is_known_tag(record.tag()));
                    prop_assert_eq!(rec_bytes[0], TAG_ENTRY);
                    prop_assert_eq!(usize::from(rec_bytes[1]), ep.ciphertext.len() + AUTH_TAG_LEN);
                    prop_assert_eq!(
                        &rec_bytes[TLV_HEADER_LEN..TLV_HEADER_LEN + ep.ciphertext.len()],
                        ep.ciphertext.as_slice()
                    );
                    prop_assert_eq!(&rec_bytes[TLV_HEADER_LEN + ep.ciphertext.len()..], &ep.auth_tag);
                }
                TlvRecord::Unknown { tag, raw_bytes } => {
                    prop_assert!(!is_known_tag(*tag));
                    prop_assert_ne!(*tag, TAG_ENTRY);
                    prop_assert_eq!(rec_bytes[0], *tag);
                    prop_assert_eq!(usize::from(rec_bytes[1]), raw_bytes.len());
                    prop_assert_eq!(&rec_bytes[TLV_HEADER_LEN..], raw_bytes.as_slice());
                }
            }

            let mut rec_chain = rec_bytes;
            rec_chain.extend_from_slice(&trailing);
            let (restored_rec, rec_rest) = deserialize_record(&rec_chain)
                .map_err(|e| TestCaseError::fail(format!("レコード復元失敗: {e:?}")))?;
            assert_record_eq(&restored_rec, &record)?;
            prop_assert_eq!(rec_rest, trailing.as_slice());
        }

        /// `tlv_vault_roundtrip` / `tlv_vault_roundtrip_sound` /
        /// `tlv_serialize_vault_bytes_header` に対応する全体可逆性およびワイヤーレイアウト検証。
        #[test]
        fn prop_mixed_vault_roundtrip_and_wire_model(
            vault_spec in arb_mixed_vault_spec(),
            trailing in arb_trailing_bytes(),
        ) {
            let vault = vault_spec.to_vault();
            let bytes = serialize(&vault)
                .map_err(|e| TestCaseError::fail(format!("Vaultシリアライズ失敗: {e:?}")))?;
            prop_assert_eq!(bytes.len(), bytes.capacity());

            // `TlvRoundtrip.v` の `tlv_serialize_vault_bytes` 純粋関数仕様とのバイト単位一致検証。
            let expected_header = serialize_header(&vault.header);
            prop_assert_eq!(&bytes[..VAULT_HEADER_LEN], &expected_header[..]);
            prop_assert_eq!(usize::from(bytes[VAULT_HEADER_LEN]), vault.slots.len());

            let mut cursor = VAULT_HEADER_LEN + 1;
            for slot in &vault.slots {
                let s_bytes = serialize_slot_entry(slot)
                    .map_err(|e| TestCaseError::fail(format!("スロットシリアライズ失敗: {e:?}")))?;
                prop_assert_eq!(&bytes[cursor..cursor + s_bytes.len()], s_bytes.as_slice());
                cursor += s_bytes.len();
            }

            let rec_count = u16::from_be_bytes([bytes[cursor], bytes[cursor + 1]]) as usize;
            prop_assert_eq!(rec_count, vault.records.len());
            cursor += 2;

            for rec in &vault.records {
                let r_bytes = serialize_record(rec)
                    .map_err(|e| TestCaseError::fail(format!("レコードシリアライズ失敗: {e:?}")))?;
                prop_assert_eq!(&bytes[cursor..cursor + r_bytes.len()], r_bytes.as_slice());
                cursor += r_bytes.len();
            }
            prop_assert_eq!(cursor, bytes.len());

            // 残余なしの完全往復可逆性。
            let (restored, rest) = deserialize(&bytes)
                .map_err(|e| TestCaseError::fail(format!("Vaultデシリアライズ失敗: {e:?}")))?;
            prop_assert!(rest.is_empty());
            assert_vault_eq(&restored, &vault)?;

            // 再シリアライズによる標準ワイヤー表現の不変性。
            let reserialized = serialize(&restored)
                .map_err(|e| TestCaseError::fail(format!("Vault再シリアライズ失敗: {e:?}")))?;
            prop_assert_eq!(reserialized, bytes.as_slice());

            // 末尾に任意の残余バイト列を伴う状態での可逆性。
            let mut with_trailing = bytes;
            with_trailing.extend_from_slice(&trailing);
            let (restored_chain, rest_chain) = deserialize(&with_trailing)
                .map_err(|e| TestCaseError::fail(format!("残余付きVault復元失敗: {e:?}")))?;
            assert_vault_eq(&restored_chain, &vault)?;
            prop_assert_eq!(rest_chain, trailing.as_slice());
        }

        /// `tlv_unknown_tag_structure_preservation` / `tlv_records_preserve_unknown_fields` /
        /// `tlv_vault_preserve_unknown_fields` に対応する未知タグのバイト不変性、
        /// および既知エントリ編集を跨いだ前方互換性検証。
        #[test]
        fn prop_unknown_tag_byte_invariance_and_preservation(
            vault_spec in arb_mixed_vault_spec(),
            new_known_spec in arb_entry_spec(),
            xor_mask in 1u8..=u8::MAX,
            drop_first_known in any::<bool>(),
        ) {
            let vault = vault_spec.to_vault();
            let expected_unknowns = extract_unknown_records(&vault.records);
            let original_unknown_wire: Vec<Vec<u8>> = vault
                .records
                .iter()
                .filter(|r| !is_known_tag(r.tag()))
                .map(|r| serialize_record(r).expect("未知レコードのシリアライズに成功。"))
                .collect();

            // 第1往復: 未知タグの脱落・順序変化・バイト破損が発生しないことを検証。
            let serialized = serialize(&vault)
                .map_err(|e| TestCaseError::fail(format!("Vaultシリアライズ失敗: {e:?}")))?;
            let (mut deserialized, rest) = deserialize(&serialized)
                .map_err(|e| TestCaseError::fail(format!("Vaultデシリアライズ失敗: {e:?}")))?;
            prop_assert!(rest.is_empty());

            let deserialized_unknowns = extract_unknown_records(&deserialized.records);
            prop_assert_eq!(&deserialized_unknowns, &expected_unknowns);

            for (idx, rec) in deserialized
                .records
                .iter()
                .filter(|r| !is_known_tag(r.tag()))
                .enumerate()
            {
                if let TlvRecord::Unknown { tag, raw_bytes } = rec {
                    prop_assert_ne!(*tag, TAG_ENTRY);
                    prop_assert!(raw_bytes.len() <= usize::from(u8::MAX));
                    let wire = serialize_record(rec)
                        .map_err(|e| TestCaseError::fail(format!("未知レコード再シリアライズ失敗: {e:?}")))?;
                    prop_assert_eq!(&wire, &original_unknown_wire[idx]);
                }
            }

            // 既知エントリのみを更新・削除・追記する旧クライアント操作を模擬。
            if let Some(next_header) = deserialized.header.checked_increment_epoch() {
                deserialized.header = next_header;
            }
            let mut dropped_one = false;
            let mut updated_records = Vec::with_capacity(deserialized.records.len() + 1);
            for rec in deserialized.records {
                match rec {
                    TlvRecord::Entry(mut payload) => {
                        if drop_first_known && !dropped_one {
                            dropped_one = true;
                            continue;
                        }
                        if let Some(first_byte) = payload.ciphertext.first_mut() {
                            *first_byte ^= xor_mask;
                        } else {
                            payload.auth_tag[0] ^= xor_mask;
                        }
                        updated_records.push(TlvRecord::Entry(payload));
                    }
                    unknown @ TlvRecord::Unknown { .. } => {
                        updated_records.push(unknown);
                    }
                }
            }
            updated_records.push(TlvRecord::Entry(new_known_spec.to_payload()));
            deserialized.records = updated_records;

            // 第2往復: 既知エントリの追加・変更・削除後でも、未知タグの順序と生バイト列が完全不変であること。
            let reserialized = serialize(&deserialized)
                .map_err(|e| TestCaseError::fail(format!("更新後Vaultシリアライズ失敗: {e:?}")))?;
            let (reloaded, reloaded_rest) = deserialize(&reserialized)
                .map_err(|e| TestCaseError::fail(format!("更新後Vaultデシリアライズ失敗: {e:?}")))?;
            prop_assert!(reloaded_rest.is_empty());

            let reloaded_unknowns = extract_unknown_records(&reloaded.records);
            prop_assert_eq!(reloaded_unknowns, expected_unknowns);

            // ワイヤー上の各未知レコード部分バイト列も元のワイヤー断片と1ビットも違わず一致すること。
            let reloaded_unknown_wire: Vec<Vec<u8>> = reloaded
                .records
                .iter()
                .filter(|r| !is_known_tag(r.tag()))
                .map(|r| serialize_record(r).expect("未知レコード再シリアライズに成功。"))
                .collect();
            prop_assert_eq!(reloaded_unknown_wire, original_unknown_wire);
        }

        /// `TlvRecord::new_unknown` およびサイズ上限超過時における健全性保護契約を検証する。
        #[test]
        fn prop_roundtrip_guard_invariants(
            raw_bytes in prop::collection::vec(any::<u8>(), 0..=300),
            oversized_ct_extra in 1usize..=64,
            oversized_unk_extra in 1usize..=64,
        ) {
            // TAG_ENTRY を Unknown へ混入させない型保護。
            prop_assert_eq!(
                TlvRecord::new_unknown(TAG_ENTRY, raw_bytes.clone()).err(),
                Some(TlvParseError::InvalidFormat)
            );
            let forged_unknown = TlvRecord::Unknown {
                tag: TAG_ENTRY,
                raw_bytes,
            };
            prop_assert_eq!(record_serialized_len(&forged_unknown), Err(TlvParseError::InvalidFormat));
            prop_assert_eq!(serialize_record(&forged_unknown), Err(TlvParseError::InvalidFormat));

            // 255バイト上限超過に対する保護。
            let oversized_ct = vec![0x42u8; (u8::MAX as usize) - AUTH_TAG_LEN + oversized_ct_extra];
            let oversized_entry = TlvRecord::Entry(EntryPayload::new(oversized_ct, [0x11; AUTH_TAG_LEN]));
            prop_assert_eq!(record_serialized_len(&oversized_entry), Err(TlvParseError::InvalidLength));
            prop_assert_eq!(serialize_record(&oversized_entry), Err(TlvParseError::InvalidLength));

            let oversized_raw = vec![0x99u8; (u8::MAX as usize) + oversized_unk_extra];
            let oversized_unknown = TlvRecord::new_unknown(99, oversized_raw)
                .map_err(|e| TestCaseError::fail(format!("未知レコード生成失敗: {e:?}")))?;
            prop_assert_eq!(record_serialized_len(&oversized_unknown), Err(TlvParseError::InvalidLength));
            prop_assert_eq!(serialize_record(&oversized_unknown), Err(TlvParseError::InvalidLength));
        }
    }

    #[test]
    fn test_vault_max_slot_count_boundary_255_and_256() {
        let header = VaultHeader::new(1, 1, 1);
        let slot = KekSlotEntry::new(0, 1, vec![0xaa, 0xbb]).expect("スロット生成に成功。");

        let vault_255 = Vault::new(header, vec![slot.clone(); 255], Vec::new());
        let bytes_255 = serialize(&vault_255).expect("255スロットのシリアライズに成功。");
        let (restored, rest) = deserialize(&bytes_255).expect("255スロットの復元に成功。");
        assert!(rest.is_empty());
        assert_eq!(restored.slots.len(), 255);
        assert!(restored == vault_255);

        let vault_256 = Vault::new(header, vec![slot; 256], Vec::new());
        assert_eq!(
            serialize(&vault_256).err(),
            Some(TlvParseError::InvalidLength)
        );
    }

    #[test]
    fn test_slot_entry_u16_max_boundary_roundtrip() {
        let max_dek = vec![0x5cu8; usize::from(u16::MAX)];
        let slot = KekSlotEntry::new(2, 2, max_dek).expect("u16::MAX長のwrapped_dek生成に成功。");
        let bytes = serialize_slot_entry(&slot).expect("u16::MAX長スロットのシリアライズに成功。");
        assert_eq!(bytes.len(), KEK_SLOT_HEADER_LEN + usize::from(u16::MAX));

        let (restored, rest) =
            deserialize_slot_entry(&bytes).expect("u16::MAX長スロットの復元に成功。");
        assert!(rest.is_empty());
        assert!(restored == slot);

        let oversized_dek = vec![0x5cu8; usize::from(u16::MAX) + 1];
        assert_eq!(
            KekSlotEntry::new(2, 2, oversized_dek).err(),
            Some(TlvParseError::InvalidLength)
        );
    }
}

#[cfg(feature = "profile-vault")]
mod crypto_vault_roundtrip_tests {
    use super::*;
    use fidelogic_core::tlv::{
        AUTH_TAG_LEN, EntryPayload, TAG_ENTRY, TlvRecord, Vault, deserialize, is_known_tag,
        serialize,
    };
    use fidelogic_core::{
        CipherSuiteId, DEK_LEN, SLOT1_MIN_PRF_LEN, SLOT1_NONCE_LEN, SLOT1_SALT_LEN, SecretBytes,
        VaultCipher, VaultEngine, XCHACHA20_POLY1305_NONCE_LEN, wrap_dek_slot1_for_header,
    };

    /// `CipherSuiteId` を選択するストラテジ。
    fn arb_cipher_suite() -> impl Strategy<Value = CipherSuiteId> {
        prop_oneof![
            Just(CipherSuiteId::XChaCha20Poly1305),
            Just(CipherSuiteId::Aes256GcmSiv),
        ]
    }

    /// 暗号化可能な既知エントリ平文(最大ノンス24Bを除いた215B以下)を生成するストラテジ。
    fn arb_plaintext_entry() -> impl Strategy<Value = ([u8; XCHACHA20_POLY1305_NONCE_LEN], Vec<u8>)>
    {
        let max_pt_len = (u8::MAX as usize) - AUTH_TAG_LEN - XCHACHA20_POLY1305_NONCE_LEN;
        (
            any::<[u8; XCHACHA20_POLY1305_NONCE_LEN]>(),
            prop::collection::vec(any::<u8>(), 0..=max_pt_len),
        )
    }

    /// 未知タグレコード仕様 `(tag, raw_bytes)` を生成するストラテジ。
    fn arb_unknown_spec() -> impl Strategy<Value = (u8, Vec<u8>)> {
        (
            (0u8..=u8::MAX).prop_filter("TAG_ENTRYは除外。", |&tag| tag != TAG_ENTRY),
            prop::collection::vec(any::<u8>(), 0..=usize::from(u8::MAX)),
        )
    }

    proptest! {
        #![proptest_config(roundtrip_proptest_config(512))]

        /// 暗号スイート・Slot 1 ラップ済み DEK・AEAD 暗号化エントリ・未知タグ混在 Vault の、
        /// シリアライズ/デシリアライズ/解錠/復号/更新を跨ぐラウンドトリップおよび未知タグ不変性を検証する。
        #[test]
        fn prop_encrypted_mixed_vault_roundtrip_and_unknown_invariance(
            suite in arb_cipher_suite(),
            version in any::<u8>(),
            epoch_id in 1u64..u64::MAX,
            dek_raw in any::<[u8; DEK_LEN]>(),
            prf_secret in prop::collection::vec(any::<u8>(), SLOT1_MIN_PRF_LEN..=64),
            salt in any::<[u8; SLOT1_SALT_LEN]>(),
            slot_nonce in any::<[u8; SLOT1_NONCE_LEN]>(),
            known_entries in prop::collection::vec(arb_plaintext_entry(), 0..=6),
            unknown_specs in prop::collection::vec(arb_unknown_spec(), 0..=6),
            interleave_bits in prop::collection::vec(any::<bool>(), 0..=16),
            update_nonce in any::<[u8; XCHACHA20_POLY1305_NONCE_LEN]>(),
            update_plaintext in prop::collection::vec(any::<u8>(), 0..=64),
        ) {
            let header = VaultHeader::new(version, suite.as_u8(), epoch_id);
            let aad = header.associated_data();
            let dek = SecretBytes::new(dek_raw);
            let slot1 = wrap_dek_slot1_for_header(&dek, &prf_secret, &salt, &slot_nonce, &header)
                .map_err(|e| TestCaseError::fail(format!("Slot 1 ラップ失敗: {e:?}")))?;

            let cipher = VaultCipher::new_from_secret(suite, &dek);
            let nonce_len = suite.nonce_len();

            // 既知エントリを AEAD 暗号化して TlvRecord::Entry 化。
            let mut known_records = Vec::with_capacity(known_entries.len());
            for (raw_nonce, pt) in &known_entries {
                let nonce = &raw_nonce[..nonce_len];
                let mut buf = pt.clone();
                let tag = cipher
                    .encrypt_in_place_detached(nonce, &aad, &mut buf)
                    .map_err(|e| TestCaseError::fail(format!("AEAD暗号化失敗: {e:?}")))?;
                let mut payload_ct = Vec::with_capacity(nonce_len + buf.len());
                payload_ct.extend_from_slice(nonce);
                payload_ct.extend_from_slice(&buf);
                known_records.push(TlvRecord::Entry(EntryPayload::new(payload_ct, tag)));
            }

            // 未知レコードを混在配置。
            let unknown_records: Vec<TlvRecord> = unknown_specs
                .iter()
                .map(|(tag, raw)| {
                    TlvRecord::new_unknown(*tag, raw.clone())
                        .expect("TAG_ENTRY以外の未知レコード生成に成功。")
                })
                .collect();

            let mut mixed_records = Vec::with_capacity(known_records.len() + unknown_records.len());
            let mut k_iter = known_records.into_iter();
            let mut u_iter = unknown_records.into_iter();
            for take_known in &interleave_bits {
                if *take_known {
                    if let Some(rec) = k_iter.next() {
                        mixed_records.push(rec);
                    } else if let Some(rec) = u_iter.next() {
                        mixed_records.push(rec);
                    }
                } else if let Some(rec) = u_iter.next() {
                    mixed_records.push(rec);
                } else if let Some(rec) = k_iter.next() {
                    mixed_records.push(rec);
                }
            }
            mixed_records.extend(k_iter);
            mixed_records.extend(u_iter);

            let vault = Vault::new(header, vec![slot1], mixed_records);
            let wire = serialize(&vault)
                .map_err(|e| TestCaseError::fail(format!("暗号化Vaultシリアライズ失敗: {e:?}")))?;
            let (deserialized, rest) = deserialize(&wire)
                .map_err(|e| TestCaseError::fail(format!("暗号化Vaultデシリアライズ失敗: {e:?}")))?;
            prop_assert!(rest.is_empty());
            prop_assert!(deserialized == vault);

            // 復元された Vault を Slot 1 で解錠し、全既知エントリの復号一致と未知タグの完全保存を検証。
            let mut engine = VaultEngine::from_slot_entries(&deserialized.slots);
            engine
                .unlock_vault_with_prf(&deserialized, &prf_secret)
                .map_err(|e| TestCaseError::fail(format!("Slot 1 解錠失敗: {e:?}")))?;
            let unlocked_dek = engine
                .dek()
                .map_err(|e| TestCaseError::fail(format!("DEK取得失敗: {e:?}")))?;
            let restored_suite = CipherSuiteId::from_u8(deserialized.header.suite_id)
                .map_err(|e| TestCaseError::fail(format!("暗号スイート変換失敗: {e:?}")))?;
            let restored_cipher = VaultCipher::new_from_secret(restored_suite, unlocked_dek);
            let restored_aad = deserialized.header.associated_data();

            let mut decrypted_knowns = Vec::new();
            let mut observed_unknowns = Vec::new();
            for rec in &deserialized.records {
                match rec {
                    TlvRecord::Entry(ep) => {
                        let n_len = restored_suite.nonce_len();
                        let mut pt_buf = ep.ciphertext[n_len..].to_vec();
                        restored_cipher
                            .decrypt_in_place_detached(
                                &ep.ciphertext[..n_len],
                                &restored_aad,
                                &mut pt_buf,
                                &ep.auth_tag,
                            )
                            .map_err(|e| TestCaseError::fail(format!("AEAD復号失敗: {e:?}")))?;
                        decrypted_knowns.push(pt_buf);
                    }
                    TlvRecord::Unknown { tag, raw_bytes } => {
                        observed_unknowns.push((*tag, raw_bytes.clone()));
                    }
                }
            }

            let expected_plaintexts: Vec<Vec<u8>> =
                known_entries.iter().map(|(_, pt)| pt.clone()).collect();
            prop_assert_eq!(decrypted_knowns, expected_plaintexts);
            prop_assert_eq!(&observed_unknowns, &unknown_specs);

            // 世代更新＋新規エントリ追記後も未知タグの順序・生バイト列が完全不変であることを検証。
            let next_header = deserialized
                .header
                .checked_increment_epoch()
                .expect("epoch_id < u64::MAX のためインクリメントに成功。");
            let next_aad = next_header.associated_data();
            let next_slot1 =
                wrap_dek_slot1_for_header(unlocked_dek, &prf_secret, &salt, &slot_nonce, &next_header)
                    .map_err(|e| TestCaseError::fail(format!("次世代Slot 1 ラップ失敗: {e:?}")))?;

            let mut next_records: Vec<TlvRecord> = deserialized
                .records
                .into_iter()
                .filter(|r| !is_known_tag(r.tag()))
                .collect();
            let mut new_ct_buf = update_plaintext.clone();
            let new_tag = restored_cipher
                .encrypt_in_place_detached(&update_nonce[..nonce_len], &next_aad, &mut new_ct_buf)
                .map_err(|e| TestCaseError::fail(format!("追記エントリ暗号化失敗: {e:?}")))?;
            let mut new_payload_ct = Vec::with_capacity(nonce_len + new_ct_buf.len());
            new_payload_ct.extend_from_slice(&update_nonce[..nonce_len]);
            new_payload_ct.extend_from_slice(&new_ct_buf);
            next_records.push(TlvRecord::Entry(EntryPayload::new(new_payload_ct, new_tag)));

            let updated_vault = Vault::new(next_header, vec![next_slot1], next_records);
            let updated_wire = serialize(&updated_vault)
                .map_err(|e| TestCaseError::fail(format!("更新Vaultシリアライズ失敗: {e:?}")))?;
            let (reloaded, reloaded_rest) = deserialize(&updated_wire)
                .map_err(|e| TestCaseError::fail(format!("更新Vaultデシリアライズ失敗: {e:?}")))?;
            prop_assert!(reloaded_rest.is_empty());

            let reloaded_unknowns: Vec<(u8, Vec<u8>)> = reloaded
                .records
                .iter()
                .filter_map(|r| match r {
                    TlvRecord::Entry(_) => None,
                    TlvRecord::Unknown { tag, raw_bytes } => Some((*tag, raw_bytes.clone())),
                })
                .collect();
            prop_assert_eq!(reloaded_unknowns, unknown_specs);
        }
    }
}
