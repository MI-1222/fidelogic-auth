//! # profile-vault モジュール。
//!
//! 完全なVault運用および高強度暗号処理を提供するプロファイル骨格。
//! Argon2id、XChaCha20-Poly1305、AES-GCM-SIVなどの暗号スイートを統括する。

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
