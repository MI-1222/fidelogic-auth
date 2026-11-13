//! # fidelogic-core
//!
//! 高セキュリティ認証・暗号化ストレージ基盤を提供するコアライブラリ。
//! `no_std` 環境および WebAssembly (Wasm) での安全かつ決定論的な動作に対応する。
//!
//! ## Architecture
//!
//! 本クレートは、厳格なメモリ隔離 (ゼロ消去・ページロック)、定数時間比較によるサイドチャネル攻撃耐性、
//! ならびに形式検証 (Rocq) に裏打ちされたエンベロープ状態機械を基盤とする。
//! アプリケーションの要件およびリソース制約に応じて、フィーチャーフラグによる二重プロファイル構成を提供する。
//!
//! - **profile-lite**: エッジ環境およびブラウザ初期認証向けの極小バイナリプロファイル。
//!   PRECIS フレームワーク (ユーザー名・パスワード正準化) および Curve25519 スカラー乗算のみを含み、
//!   メモリ・ストレージ制約の極めて厳しい実行環境に最適化される。
//! - **profile-vault**: 完全な暗号化ストレージ (Vault) 運用および多重暗号スイートを提供するプロファイル。
//!   ゼロコピー TLV パース、Argon2id / HKDF 鍵導出、XChaCha20-Poly1305 / AES-256-GCM-SIV AEAD、
//!   ならびに多重スロット (パスワード、WebAuthn PRF、リカバリーコード) によるエンベロープ復号を統括する。
//!
//! ## Security
//!
//! - **確定的なメモリ消去**: 機密データ構造体 ([`SecretBytes`], [`SecretVec`]) は、ドロップ時および
//!   エラー発生時に `volatile` 書き込みとコンパイラフェンスを用いて確実にゼロクリアされる。
//! - **サイドチャネル攻撃防御**: 鍵比較や認証タグ検証は、ビット論理演算に基づく定数時間演算関数群
//!   ([`ct_eq_bytes`], [`ct_eq_32`] 等) により分岐を排除して実行される。
//! - **形式仕様との対応**: エンベロープ暗号化状態機械 (`VaultEngine`) の安全性不変条件 (`SafeState`)
//!   および鍵非干渉性 (`NonInterference`) は、Rocq による厳密な機械検証仕様に整合する。

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
pub use zeroize::{SecretBytes, volatile_zeroize, volatile_zeroize_words};

#[cfg(feature = "alloc")]
pub use zeroize::SecretVec;

#[cfg(feature = "memlock")]
pub use memlock::LockedBuffer;

#[cfg_attr(doc, aquamarine::aquamarine)]
/// 現在コンパイル時に有効化されているプロファイルの識別子を返す。
///
/// 本クレートは Cargo のフィーチャーフラグ制御に基づき、実行環境に応じた最適な機能セットを
/// 決定論的に選択する。
///
/// # プロファイル構成とモジュール包含関係
///
/// ```mermaid
/// stateDiagram-v2
///     state "FidelogicCore （コアクレート）" as Core {
///         state "共通基盤層" as Common {
///             error
///             zeroize
///             constant_time
///             memlock
///         }
///         state "profile-lite （極小フットプリント）" as Lite {
///             precis
///             curve25519
///         }
///         state "profile-vault （完全機能Vault）" as Vault {
///             tlv
///             cipher
///             kdf
///             envelope
///             slots
///         }
///     }
/// ```
///
/// # Returns
///
/// - `"profile-vault"`: `profile-vault` フィーチャーが有効な場合 (完全機能)。
/// - `"profile-lite"`: `profile-vault` が無効で `profile-lite` のみが有効な場合。
/// - `"none"`: いずれのプロファイルフィーチャーも有効化されていない場合。
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
