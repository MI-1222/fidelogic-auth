//! # profile-vault モジュール。
//!
//! 完全なVault運用および高強度暗号処理を提供するプロファイル骨格。
//! Argon2id、XChaCha20-Poly1305、AES-GCM-SIVなどの暗号スイートを統括する。

pub use crate::tlv::{
    KEK_SLOT_ENTRY_LEN, KekSlotEntry, TAG_ENTRY, TlvParseError, VAULT_HEADER_LEN, VAULT_MAGIC,
    VaultError, VaultHeader, deserialize_header, deserialize_slot_entry, is_known_tag,
};
#[cfg(feature = "alloc")]
pub use crate::tlv::{TlvPayload, TlvRecord, Vault, deserialize, deserialize_record};

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
        };
        let vault = Vault::new(header, alloc::vec::Vec::new(), alloc::vec::Vec::new());
        assert_eq!(
            vault.header, header,
            "profile_vault経由のVault生成と比較に成功。"
        );
    }

    #[test]
    fn test_vault_error_reexport() {
        let err = VaultError::InvalidMagic;
        let parse_err: TlvParseError = err;
        assert_eq!(
            parse_err,
            VaultError::InvalidMagic,
            "profile_vault経由のVaultError再エクスポート確認に成功。"
        );
    }

    #[test]
    fn test_deserialize_header_reexport() {
        let input = [b'F', b'V', b'A', b'U', 1, 1];
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
            Err(VaultError::InvalidLength),
            "profile_vault経由のdeserialize_record呼び出しに成功。"
        );
    }

    #[test]
    fn test_deserialize_slot_entry_reexport() {
        let input = [0, 1, 0, 64];
        let res = deserialize_slot_entry(&input);
        assert!(
            res.is_ok(),
            "profile_vault経由のdeserialize_slot_entry呼び出しに成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_vault_reexport() {
        let input = [b'F', b'V', b'A', b'U', 1, 1, 0, 0x00, 0x00];
        let res = deserialize(&input);
        assert!(
            res.is_ok(),
            "profile_vault経由のdeserialize呼び出しに成功。"
        );
    }
}
