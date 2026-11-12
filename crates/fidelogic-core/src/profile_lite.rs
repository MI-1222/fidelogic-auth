//! # profile-lite モジュール。
//!
//! エッジ環境およびブラウザ初期認証向けの軽量プロファイル骨格。
//! OPAQUEプロトコル検証やゼロコピーTLVパースなどの最小処理を提供する。

pub use crate::error::PrecisError;
pub use crate::precis::*;

/// `profile-lite` の初期化状態およびエンジンを表す構造体。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct LiteProfileEngine;

impl LiteProfileEngine {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

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
            Ok(alloc::string::String::from("alice")),
            "profile_lite経由のusername_case_mapped呼び出しに成功。"
        );
        assert_eq!(
            username_case_mapped("bad name"),
            Err(PrecisError::DisallowedCodePoint(0x0020)),
            "profile_lite経由のPrecisError返却確認に成功。"
        );
        assert_eq!(
            opaque_string("Pass Word"),
            Ok(alloc::string::String::from("Pass Word")),
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
