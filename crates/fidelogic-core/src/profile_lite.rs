//! # profile-lite モジュール。
//!
//! リソース制約の厳しいエッジ環境やブラウザ初期認証に特化した極小バイナリプロファイル。
//! RFC 7564 / RFC 8265 PRECIS フレームワーク (ユーザー名・パスワードの正準化) および
//! Curve25519 楕円曲線暗号プリミティブ (Diffie-Hellman 鍵交換) を再エクスポートする。
//!
//! ## 適用対象と設計目標
//!
//! 本プロファイルは、バイナリサイズおよび初期ロード時間の削減が最重要視される WebAssembly ターゲットや
//! 組み込みデバイスを主な対象とする。Argon2id や AEAD 暗号化 Vault などの重量級ロジックをコンパイルから除外し、
//! 認証前処理および事前共有鍵合意に必要な最小限のセキュア基盤のみを極小フットプリントで提供する。

pub use crate::error::PrecisError;
pub use crate::precis::*;

/// `profile-lite` の初期化状態およびエンジンコンテキストを表現する構造体。
///
/// 軽量プロファイル環境における識別情報と静的ディスパッチ境界をカプセル化する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct LiteProfileEngine;

impl LiteProfileEngine {
    /// 新しい `LiteProfileEngine` インスタンスを構築する。
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    /// プロファイル名識別子 (`"profile-lite"`) を返す。
    #[must_use]
    pub const fn name(&self) -> &'static str {
        "profile-lite"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "alloc")]
    #[test]
    fn test_precis_reexport() {
        assert_eq!(
            username_case_mapped("Alice"),
            Ok(Zeroizing::new(alloc::string::String::from("alice"))),
            "profile_lite経由のusername_case_mapped呼び出しに成功。"
        );
        assert_eq!(
            username_case_mapped("bad name"),
            Err(PrecisError::DisallowedCodePoint(0x0020)),
            "profile_lite経由のPrecisError返却確認に成功。"
        );
        assert_eq!(
            opaque_string("Pass Word"),
            Ok(Zeroizing::new(alloc::string::String::from("Pass Word"))),
            "profile_lite経由のopaque_string呼び出しに成功。"
        );
        assert_eq!(
            opaque_string("bad\0pw"),
            Err(PrecisError::DisallowedCodePoint(0x0000)),
            "profile_lite経由のopaque_string禁止文字拒絶確認に成功。"
        );
        assert_eq!(
            opaque_string_secret("Pass Word")
                .expect("profile_lite経由のopaque_string_secret呼び出しに成功。")
                .as_slice(),
            b"Pass Word"
        );
    }
}
