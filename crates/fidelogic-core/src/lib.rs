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
#[cfg(feature = "profile-vault")]
pub mod slots;
pub mod tlv;
pub mod zeroize;

#[cfg(feature = "profile-vault")]
pub use cipher::{
    AES_256_GCM_SIV_NONCE_LEN, CipherSuiteId, KEY_LEN, MAX_AAD_LEN, MAX_PAYLOAD_LEN, TAG_LEN,
    VaultCipher, XCHACHA20_POLY1305_NONCE_LEN,
};
pub use constant_time::{
    ct_assign_slice, ct_eq_32, ct_eq_array, ct_eq_bytes, ct_eq_bytes_bool, ct_select,
    ct_select_slice,
};
#[cfg(feature = "profile-lite")]
pub use curve25519::{
    X25519PublicKey, X25519SharedSecret, edwards_basepoint_mul, ristretto_basepoint_mul,
    x25519_basepoint_mul, x25519_diffie_hellman,
};
#[cfg(feature = "profile-vault")]
pub use envelope::{
    DEK_LEN, KekSlots, SLOT_ID_ARGON2ID, SLOT_ID_PRF, SLOT_ID_RECOVERY, SlotKind, SlotStatus,
    VaultEngine, VaultEvent, VaultState,
};
pub use error::{CryptoError, SystemError, TlvParseError, VaultError};
#[cfg(feature = "profile-vault")]
pub use kdf::{
    Argon2Params, DEFAULT_KEY_LEN, DEFAULT_NATIVE_M_COST, DEFAULT_NATIVE_P_COST,
    DEFAULT_NATIVE_T_COST, DEFAULT_WASM_M_COST, DEFAULT_WASM_P_COST, DEFAULT_WASM_T_COST,
    FAST_TEST_M_COST, FAST_TEST_P_COST, FAST_TEST_T_COST, HKDF_SHA256_HASH_LEN,
    HKDF_SHA256_MAX_OUTPUT_LEN, hkdf_sha256_derive, hkdf_sha256_derive_32, hkdf_sha256_derive_vec,
};
#[cfg(feature = "profile-vault")]
pub use slots::{
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
