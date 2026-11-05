//! # profile-lite モジュール。
//!
//! エッジ環境およびブラウザ初期認証向けの軽量プロファイル骨格。
//! OPAQUEプロトコル検証やゼロコピーTLVパースなどの最小処理を提供する。

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
