//! # profile-lite モジュール。
//!
//! エッジ環境およびブラウザ初期認証向けの軽量プロファイル骨格。
//! OPAQUEプロトコル検証やゼロコピーTLVパースなどの最小処理を提供する。

pub use crate::error::PrecisError;
pub use crate::precis::{
    UNICODE_MAX_CODE_POINT, all_allowed, compose_hangul_syllable, compose_hangul_trailing,
    compose_pair, find_disallowed_cp, in_range, is_ascii_control, is_disallowed_cp,
    is_non_ascii_control, is_noncharacter, is_out_of_bounds, is_private_use, is_space,
    is_surrogate, precis_fold_char, precis_fold_cp,
};
#[cfg(feature = "alloc")]
pub use crate::precis::{
    enforce_username_case_mapped_cps, precis_fold_string, precis_nfc_normalize,
    precis_username_case_mapped, username_case_mapped,
};

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
    }
}
