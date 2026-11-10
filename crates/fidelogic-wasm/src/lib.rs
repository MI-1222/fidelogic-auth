//! # fidelogic-wasm
//!
//! WebAssembly環境向けの薄いC ABIインターフェースおよびバインディング層。
//! `profile-lite`(認証用極小バイナリ), `profile-vault`(完全Vault展開用バイナリ)のビルドターゲット。

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate std;

#[cfg(all(target_arch = "wasm32", not(feature = "std")))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

/// Wasm環境(`target_arch = "wasm32"` かつ `not(feature = "std")`)向けのグローバルアロケータ。
///
/// 断片化耐性に優れた `dlmalloc` へ一本化し、長期稼働Vaultや可変長ワークスペースでの安定したメモリ回収を保証する。
#[cfg(all(target_arch = "wasm32", not(feature = "std")))]
#[global_allocator]
static ALLOCATOR: dlmalloc::GlobalDlmalloc = dlmalloc::GlobalDlmalloc;

use fidelogic_core::active_profile;

/// 現在リンクされているコアエンジンのプロファイルステータスコードを取得する。
///
/// 外部C ABIからも直接呼び出し可能なインターフェース骨格。
#[unsafe(no_mangle)]
pub extern "C" fn fidelogic_wasm_status() -> u32 {
    let profile = active_profile();
    if profile.is_empty() { 0 } else { 1 }
}

/// Dead Store Elimination (DSE) 抑止検査用の外部C ABIエクスポート関数。
///
/// 指定されたメモリ領域に対して揮発性ゼロ書き込みを実施する。
/// 内部で [`fidelogic_core::zeroize::volatile_zeroize`] を呼び出す。
///
/// # Safety
/// 呼び出し元は `ptr` が有効であり、少なくとも `len` バイトの連続した書き込み可能メモリを指していることを保証しなければならない。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_zeroize_test(ptr: *mut u8, len: usize) {
    if ptr.is_null() || len == 0 {
        return;
    }
    // SAFETY: 関数の事前条件に基づき、`ptr` は有効かつ `len` バイトの範囲でアクセス可能。
    let slice = unsafe { core::slice::from_raw_parts_mut(ptr, len) };
    fidelogic_core::zeroize::volatile_zeroize(slice);
}

/// 定数時間暗号照合ブロック(32バイト認証タグ・トークン照合)の外部C ABIエクスポート関数。
///
/// 暗号照合ブロック内部にコンパイラ最適化による早期リターンや
/// 条件分岐命令(`br_if`, `if`, `br_table`)が注入されていないかを機械的静的検査で検証するための対象関数。
///
/// # Safety
/// 呼び出し元は `a_ptr` および `b_ptr` が有効であり、それぞれ少なくとも32バイトの連続した
/// 読み取り可能メモリ領域を指していることを保証しなければならない。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_constant_time_eq_32(
    a_ptr: *const u8,
    b_ptr: *const u8,
) -> u32 {
    let a = unsafe { &*(a_ptr as *const [u8; 32]) };
    let b = unsafe { &*(b_ptr as *const [u8; 32]) };
    fidelogic_core::ct_eq_32(a, b).unwrap_u8() as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_status() {
        assert_eq!(fidelogic_wasm_status(), 1);
    }

    #[test]
    fn test_constant_time_eq_32() {
        let tag1 = [0x42u8; 32];
        let tag2 = [0x42u8; 32];
        let mut tag3 = [0x42u8; 32];
        tag3[31] = 0x43;

        unsafe {
            assert_eq!(
                fidelogic_wasm_constant_time_eq_32(tag1.as_ptr(), tag2.as_ptr()),
                1
            );
            assert_eq!(
                fidelogic_wasm_constant_time_eq_32(tag1.as_ptr(), tag3.as_ptr()),
                0
            );
        }
    }
}
