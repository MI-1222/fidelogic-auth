//! # profile-vault モジュール。
//!
//! 完全なVault運用および高強度暗号処理を提供するプロファイル骨格。
//! Argon2id、XChaCha20-Poly1305、AES-GCM-SIVなどの暗号スイートを統括する。

pub use crate::cipher::*;
pub use crate::envelope::*;
pub use crate::error::{CryptoError, PrecisError, SystemError, TlvParseError, VaultError};
pub use crate::kdf::*;
pub use crate::profile_lite::*;
pub use crate::slots::*;
pub use crate::tlv::*;

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

    #[cfg(feature = "alloc")]
    #[test]
    fn test_precis_reexport() {
        assert_eq!(
            username_case_mapped("User"),
            Ok(Zeroizing::new(alloc::string::String::from("user"))),
            "profile_vault経由のusername_case_mapped呼び出しに成功。"
        );
        assert_eq!(
            username_case_mapped(""),
            Err(PrecisError::EmptyInput),
            "profile_vault経由のPrecisError返却確認に成功。"
        );
        assert_eq!(
            opaque_string("Pass Word\u{0020}A\u{0308}"),
            Ok(Zeroizing::new(alloc::string::String::from("Pass Word Ä"))),
            "profile_vault経由のopaque_string呼び出しに成功。"
        );
        assert_eq!(
            opaque_string_secret("Pass Word\u{0020}A\u{0308}")
                .expect("profile_vault経由のopaque_string_secret呼び出しに成功。")
                .as_slice(),
            "Pass Word Ä".as_bytes()
        );
    }
}
