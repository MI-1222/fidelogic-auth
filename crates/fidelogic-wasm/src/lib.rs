//! # fidelogic-wasm
//!
//! WebAssembly環境向けの薄いC ABIインターフェースおよびバインディング層。
//! `profile-lite`(認証用極小バイナリ), `profile-vault`(完全Vault展開用バイナリ)のビルドターゲット。

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate std;

use fidelogic_core::active_profile;

/// 現在リンクされているコアエンジンのプロファイルステータスコードを取得する。
///
/// 外部C ABIからも直接呼び出し可能なインターフェース骨格。
#[unsafe(no_mangle)]
pub extern "C" fn fidelogic_wasm_status() -> u32 {
    let profile = active_profile();
    if profile.is_empty() { 0 } else { 1 }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_status() {
        assert_eq!(fidelogic_wasm_status(), 1);
    }
}
