//! # 鍵導出失敗時のヒープ平文残留検証テスト。
//!
//! カスタムグローバルアロケータにより `dealloc` 時の解放済みメモリ内容を検査し、
//! [`Argon2Params::derive_key_vec_with_secret`] と同じ経路で出力用 [`SecretVec`] が
//! 確保された後に鍵断片が書き込まれてエラー終了した場合でも、RAII により
//! ヒープ上へ鍵データが残留しないことを検証する。

#![cfg(feature = "alloc")]

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use fidelogic_core::{Argon2Params, CryptoError};

/// ヒープ残留検査用の固定長鍵センチネル値。
const KEY_SENTINEL: &[u8; 32] = b"FIDELOGIC_DERIVED_KEY_SENTINEL!!";

static TRACKING_ACTIVE: AtomicBool = AtomicBool::new(false);
static LEAK_DETECTED: AtomicBool = AtomicBool::new(false);
static CHECKED_DEALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);

/// 解放前のヒープブロックに鍵センチネルが残っていないかを監視するテスト用アロケータ。
struct ZeroizeCheckingAllocator;

unsafe impl GlobalAlloc for ZeroizeCheckingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if TRACKING_ACTIVE.load(Ordering::SeqCst) && layout.size() >= KEY_SENTINEL.len() {
            CHECKED_DEALLOC_COUNT.fetch_add(1, Ordering::SeqCst);
            let freed_bytes = unsafe { core::slice::from_raw_parts(ptr, layout.size()) };
            if freed_bytes
                .windows(KEY_SENTINEL.len())
                .any(|window| window == KEY_SENTINEL)
            {
                LEAK_DETECTED.store(true, Ordering::SeqCst);
            }
        }
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: ZeroizeCheckingAllocator = ZeroizeCheckingAllocator;

#[test]
fn test_kdf_derive_key_vec_no_heap_residue_on_failure() {
    let params = Argon2Params::fast_test().with_output_len(64);
    let password = b"kdf-zeroize-password";
    let salt = b"kdf-zeroize-salt-1234";
    let secret = b"kdf-zeroize-pepper";

    let mut hook_called = false;
    let mut saw_key_in_heap = false;

    LEAK_DETECTED.store(false, Ordering::SeqCst);
    CHECKED_DEALLOC_COUNT.store(0, Ordering::SeqCst);
    TRACKING_ACTIVE.store(true, Ordering::SeqCst);

    let res = params.derive_key_vec_with_secret_fn(password, salt, secret, |_, _, _, out| {
        hook_called = true;
        out[..KEY_SENTINEL.len()].copy_from_slice(KEY_SENTINEL);
        saw_key_in_heap = out
            .windows(KEY_SENTINEL.len())
            .any(|window| window == KEY_SENTINEL);
        // フック側では明示的にゼロ消去せずエラーを返し、SecretVec の RAII 消去を検証する。
        Err(CryptoError::KeyDerivationFailed)
    });

    TRACKING_ACTIVE.store(false, Ordering::SeqCst);

    assert!(
        hook_called,
        "事前検証通過後に鍵導出フックが呼び出されたことを確認。"
    );
    assert!(
        saw_key_in_heap,
        "失敗直前のヒープバッファへ鍵センチネルが書き込まれていたことを確認。"
    );
    assert_eq!(
        res.err(),
        Some(CryptoError::KeyDerivationFailed),
        "鍵導出失敗エラーがそのまま返却されることを確認。"
    );
    assert!(
        CHECKED_DEALLOC_COUNT.load(Ordering::SeqCst) >= 1,
        "検査対象サイズのヒープブロックが実際に確保・解放されたことを確認。"
    );
    assert!(
        !LEAK_DETECTED.load(Ordering::SeqCst),
        "鍵導出失敗時に解放されたヒープ領域へ鍵データが残留しないことを確認。"
    );

    // 陽性対照: 通常の Vec<u8> をゼロ消去せず解放した場合にリークを検知できることを確認する。
    LEAK_DETECTED.store(false, Ordering::SeqCst);
    CHECKED_DEALLOC_COUNT.store(0, Ordering::SeqCst);
    TRACKING_ACTIVE.store(true, Ordering::SeqCst);
    {
        let leaked_vec = core::hint::black_box(KEY_SENTINEL.to_vec());
        drop(leaked_vec);
    }
    TRACKING_ACTIVE.store(false, Ordering::SeqCst);

    assert!(
        CHECKED_DEALLOC_COUNT.load(Ordering::SeqCst) >= 1,
        "陽性対照のヒープ解放が検査されたことを確認。"
    );
    assert!(
        LEAK_DETECTED.load(Ordering::SeqCst),
        "未消去バッファの解放時に検査アロケータが鍵残留を正しく検知できることを確認。"
    );
}
