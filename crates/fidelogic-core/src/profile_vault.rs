//! # profile-vault モジュール。
//!
//! 完全なVault運用および高強度暗号処理を提供するプロファイル骨格。
//! Argon2id、XChaCha20-Poly1305、AES-GCM-SIVなどの暗号スイートを統括する。

pub use crate::tlv::{KekSlotEntry, TlvParseError, VaultError, VaultHeader};
#[cfg(feature = "alloc")]
pub use crate::tlv::{TlvPayload, TlvRecord, Vault};

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
}
