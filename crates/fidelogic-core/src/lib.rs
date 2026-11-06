//! # fidelogic-core
//!
//! Fidelogicのコア暗号・認証エンジンを提供するライブラリ。
//! `no_std` 環境およびWebAssembly(Wasm)での動作に対応。
//!
//! ## プロファイル構成:
//! 本クレートはフィーチャーフラグにより二重プロファイル構成を提供する。
//! - `profile-lite`: エッジおよび高速認証向けの極小バイナリプロファイル。
//! - `profile-vault`: 完全なVault操作および多重暗号スイートを提供するプロファイル。

#![no_std]

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "profile-lite")]
pub mod profile_lite;

#[cfg(feature = "profile-vault")]
pub mod profile_vault;

pub mod tlv;
pub mod zeroize;

/// 現在有効化されているプロファイルの識別子を返す。
#[must_use]
pub fn active_profile() -> &'static str {
    #[cfg(all(feature = "profile-lite", feature = "profile-vault"))]
    {
        "hybrid (profile-lite + profile-vault)"
    }
    #[cfg(all(feature = "profile-lite", not(feature = "profile-vault")))]
    {
        "profile-lite"
    }
    #[cfg(all(not(feature = "profile-lite"), feature = "profile-vault"))]
    {
        "profile-vault"
    }
    #[cfg(all(not(feature = "profile-lite"), not(feature = "profile-vault")))]
    {
        "none"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_active_profile_not_empty() {
        let profile_name = active_profile();
        assert!(!profile_name.is_empty());
    }

    #[cfg(feature = "profile-lite")]
    #[test]
    fn test_profile_lite_engine() {
        let engine = profile_lite::LiteProfileEngine::new();
        assert_eq!(engine.name(), "profile-lite");
    }

    #[cfg(feature = "profile-vault")]
    #[test]
    fn test_profile_vault_engine() {
        let engine = profile_vault::VaultProfileEngine::new();
        assert_eq!(engine.name(), "profile-vault");
    }
}
