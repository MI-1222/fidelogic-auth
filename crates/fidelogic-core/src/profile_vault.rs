//! # profile-vault モジュール。
//!
//! 完全なVault運用および高強度暗号処理を提供するプロファイル骨格。
//! Argon2id、XChaCha20-Poly1305、AES-GCM-SIVなどの暗号スイートを統括する。

pub use crate::cipher::{
    AES_256_GCM_SIV_NONCE_LEN, CipherSuiteId, KEY_LEN, MAX_AAD_LEN, MAX_PAYLOAD_LEN, TAG_LEN,
    VaultCipher, XCHACHA20_POLY1305_NONCE_LEN,
};
pub use crate::envelope::{
    DEK_LEN, KekSlots, SLOT_ID_ARGON2ID, SLOT_ID_PRF, SLOT_ID_RECOVERY, SlotKind, SlotStatus,
    VaultEngine, VaultEvent, VaultState,
};
pub use crate::error::{CryptoError, SystemError, TlvParseError, VaultError};
pub use crate::kdf::{
    HKDF_SHA256_HASH_LEN, HKDF_SHA256_MAX_OUTPUT_LEN, hkdf_sha256_derive, hkdf_sha256_derive_32,
    hkdf_sha256_derive_vec,
};
pub use crate::slots::{
    Argon2idSlotPayload, KDF_KIND_ARGON2ID, KDF_KIND_HKDF_SHA256, KDF_KIND_RECOVERY, KdfKind,
    MAX_SLOT0_M_COST, MAX_SLOT0_P_COST, MAX_SLOT0_T_COST, PrfSlotPayload, RecoverySlotPayload,
    SLOT_CIPHER_SUITE, SLOT0_CIPHERTEXT_LEN, SLOT0_NONCE_LEN, SLOT0_PARAMS_LEN, SLOT0_SALT_LEN,
    SLOT0_TAG_LEN, SLOT0_WRAPPED_DEK_LEN, SLOT1_CIPHERTEXT_LEN, SLOT1_MIN_PRF_LEN, SLOT1_NONCE_LEN,
    SLOT1_SALT_LEN, SLOT1_TAG_LEN, SLOT1_WRAPPED_DEK_LEN, SLOT2_CIPHERTEXT_LEN, SLOT2_MIN_CODE_LEN,
    SLOT2_MIN_SECRET_LEN, SLOT2_NONCE_LEN, SLOT2_SALT_LEN, SLOT2_TAG_LEN, SLOT2_WRAPPED_DEK_LEN,
    SlotCredential, find_slot_entry, inspect_kek_slots, is_valid_slot0_entry, is_valid_slot1_entry,
    is_valid_slot2_entry, normalize_recovery_code, unwrap_dek_slot0, unwrap_dek_slot0_for_header,
    unwrap_dek_slot0_with_secret, unwrap_dek_slot1, unwrap_dek_slot1_for_header, unwrap_dek_slot2,
    unwrap_dek_slot2_code, unwrap_dek_slot2_code_for_header, unwrap_dek_slot2_for_header,
    validate_slot0_argon2_params, wrap_dek_slot0, wrap_dek_slot0_for_header,
    wrap_dek_slot0_with_secret, wrap_dek_slot1, wrap_dek_slot1_for_header, wrap_dek_slot2,
    wrap_dek_slot2_code, wrap_dek_slot2_code_for_header, wrap_dek_slot2_for_header,
};
#[cfg(feature = "alloc")]
pub use crate::tlv::{
    EntryPayload, KekSlotEntry, TlvPayload, TlvRecord, Vault, deserialize, deserialize_record,
    deserialize_slot_entry, record_serialized_len, serialize, serialize_record,
    serialize_record_into, serialize_slot_entry, serialize_slot_entry_into, slot_serialized_len,
};
pub use crate::tlv::{
    KEK_SLOT_ENTRY_LEN, KEK_SLOT_HEADER_LEN, TAG_ENTRY, TLV_HEADER_LEN, VAULT_HEADER_LEN,
    VAULT_MAGIC, VaultHeader, deserialize_header, is_known_tag, serialize_header,
};

/// `profile-vault` の運用エンジンを表す構造体。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct VaultProfileEngine;

impl VaultProfileEngine {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    #[must_use]
    pub const fn name(&self) -> &'static str {
        "profile-vault"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vault_reexport() {
        let header = VaultHeader {
            magic: crate::tlv::VAULT_MAGIC,
            version: 1,
            suite_id: 1,
            epoch_id: 1,
        };
        let vault = Vault::new(header, alloc::vec::Vec::new(), alloc::vec::Vec::new());
        assert_eq!(
            vault.header, header,
            "profile_vault経由のVault生成と比較に成功。"
        );
    }

    #[test]
    fn test_vault_error_reexport() {
        let parse_err = TlvParseError::InvalidMagic;
        let vault_err: VaultError = parse_err.into();
        assert_eq!(
            vault_err,
            VaultError::Parse(TlvParseError::InvalidMagic),
            "profile_vault経由のVaultError再エクスポートおよびFrom変換確認に成功。"
        );
        let crypto_err = CryptoError::KeyDerivationFailed;
        let vault_crypto: VaultError = crypto_err.into();
        assert_eq!(
            vault_crypto,
            VaultError::Crypto(CryptoError::KeyDerivationFailed),
            "profile_vault経由のCryptoError変換確認に成功。"
        );
        let system_err = SystemError::MemoryLockFailed;
        let vault_system: VaultError = system_err.into();
        assert_eq!(
            vault_system,
            VaultError::System(SystemError::MemoryLockFailed),
            "profile_vault経由のSystemError変換確認に成功。"
        );
    }

    #[test]
    fn test_deserialize_header_reexport() {
        let input = [b'F', b'V', b'A', b'U', 1, 1, 0, 0, 0, 0, 0, 0, 0, 1];
        let res = deserialize_header(&input);
        assert!(
            res.is_ok(),
            "profile_vault経由のdeserialize_header呼び出しに成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_record_reexport() {
        let input = [TAG_ENTRY, 0];
        let res = deserialize_record(&input);
        assert_eq!(
            res,
            Err(TlvParseError::InvalidLength),
            "profile_vault経由のdeserialize_record呼び出しに成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_slot_entry_reexport() {
        let input = [0, 1, 0, 4, 1, 2, 3, 4];
        let res = deserialize_slot_entry(&input);
        assert!(
            res.is_ok(),
            "profile_vault経由のdeserialize_slot_entry呼び出しに成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_vault_reexport() {
        let input = [
            b'F', b'V', b'A', b'U', 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0x00, 0x00,
        ];
        let res = deserialize(&input);
        assert!(
            res.is_ok(),
            "profile_vault経由のdeserialize呼び出しに成功。"
        );
    }

    #[test]
    fn test_serialize_header_reexport() {
        let header = VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: 1,
            epoch_id: 1,
        };
        let bytes = serialize_header(&header);
        assert_eq!(
            bytes,
            [b'F', b'V', b'A', b'U', 1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
            "profile_vault経由のserialize_header呼び出しに成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_slot_entry_reexport() {
        let entry = KekSlotEntry::new(0, 1, alloc::vec![1, 2, 3, 4])
            .expect("KEKスロットエントリ生成に成功。");
        let bytes = serialize_slot_entry(&entry).expect("シリアライズに成功。");
        assert_eq!(
            bytes,
            [0, 1, 0, 4, 1, 2, 3, 4],
            "profile_vault経由のserialize_slot_entry呼び出しに成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_record_reexport() {
        let record =
            TlvRecord::new_unknown(99, alloc::vec![1, 2, 3]).expect("未知レコードの生成に成功。");
        let res = serialize_record(&record);
        assert!(
            res.is_ok(),
            "profile_vault経由のserialize_record呼び出しに成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_vault_reexport() {
        let header = VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: 1,
            epoch_id: 1,
        };
        let vault = Vault::new(header, alloc::vec::Vec::new(), alloc::vec::Vec::new());
        let res = serialize(&vault);
        assert!(res.is_ok(), "profile_vault経由のserialize呼び出しに成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialized_len_helpers_reexport() {
        let slot = KekSlotEntry::new(0, 1, alloc::vec![1, 2, 3, 4])
            .expect("KEKスロットエントリ生成に成功。");
        let slot_len = slot_serialized_len(&slot).expect("スロット長計算に成功。");
        assert_eq!(
            slot_len,
            KEK_SLOT_HEADER_LEN + 4,
            "profile_vault経由のslot_serialized_len呼び出しに成功。"
        );

        let record =
            TlvRecord::new_unknown(99, alloc::vec![1, 2, 3]).expect("未知レコードの生成に成功。");
        let record_len = record_serialized_len(&record).expect("レコード長計算に成功。");
        assert_eq!(
            record_len,
            TLV_HEADER_LEN + 3,
            "profile_vault経由のrecord_serialized_len呼び出しに成功。"
        );
    }

    #[test]
    fn test_vault_cipher_reexport() {
        let key = [0x5au8; KEY_LEN];
        let cipher = VaultCipher::new(CipherSuiteId::XChaCha20Poly1305, &key);
        assert_eq!(
            cipher.suite_id(),
            CipherSuiteId::XChaCha20Poly1305,
            "profile_vault経由のVaultCipher生成と再エクスポート検証に成功。"
        );
        assert_eq!(
            cipher.nonce_len(),
            XCHACHA20_POLY1305_NONCE_LEN,
            "profile_vault経由のノンス長取得に成功。"
        );
    }
}
