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

#[cfg(feature = "memlock")]
pub mod memlock;

#[cfg(feature = "profile-vault")]
pub mod cipher;
pub mod constant_time;
#[cfg(feature = "profile-lite")]
pub mod curve25519;
#[cfg(feature = "profile-vault")]
pub mod envelope;
pub mod error;
#[cfg(feature = "profile-vault")]
pub mod kdf;
pub mod precis;
#[cfg(feature = "profile-vault")]
pub mod slots;
pub mod tlv;
pub mod zeroize;

#[cfg(feature = "profile-vault")]
pub use profile_vault::*;

#[cfg(all(feature = "profile-lite", not(feature = "profile-vault")))]
pub use profile_lite::*;

#[cfg(not(feature = "profile-vault"))]
pub use error::{CryptoError, PrecisError, SystemError, TlvParseError, VaultError};

#[cfg(all(not(feature = "profile-lite"), not(feature = "profile-vault")))]
pub use precis::*;

pub use constant_time::{
    ct_assign_slice, ct_eq_32, ct_eq_array, ct_eq_bytes, ct_eq_bytes_bool, ct_select,
    ct_select_slice,
};
#[cfg(feature = "profile-lite")]
pub use curve25519::{
    X25519PublicKey, X25519SharedSecret, edwards_basepoint_mul, ristretto_basepoint_mul,
    x25519_basepoint_mul, x25519_diffie_hellman,
};
pub use zeroize::{SecretBytes, volatile_zeroize};

#[cfg(feature = "alloc")]
pub use zeroize::SecretVec;

#[cfg(feature = "memlock")]
pub use memlock::LockedBuffer;

/// 現在有効化されているプロファイルの識別子を返す。
#[must_use]
pub fn active_profile() -> &'static str {
    #[cfg(feature = "profile-vault")]
    {
        "profile-vault"
    }
    #[cfg(all(feature = "profile-lite", not(feature = "profile-vault")))]
    {
        "profile-lite"
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

        #[cfg(feature = "profile-vault")]
        assert_eq!(profile_name, "profile-vault");
        #[cfg(all(feature = "profile-lite", not(feature = "profile-vault")))]
        assert_eq!(profile_name, "profile-lite");
        #[cfg(all(not(feature = "profile-lite"), not(feature = "profile-vault")))]
        assert_eq!(profile_name, "none");
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

    #[cfg(feature = "memlock")]
    #[test]
    fn test_memlock_locked_buffer_export() {
        let buf = LockedBuffer::<32>::zero();
        assert_eq!(
            buf.len(),
            32,
            "エクスポートされたLockedBufferの生成に成功。"
        );
    }

    #[cfg(feature = "profile-lite")]
    #[test]
    fn test_curve25519_export() {
        let private_key = SecretBytes::new([1u8; 32]);
        let public_key = x25519_basepoint_mul(&private_key);
        assert_ne!(
            public_key.as_bytes(),
            &[0u8; 32],
            "エクスポートされたX25519ベースポイント乗算に成功。"
        );
    }
}
