//! # 暗号化失敗時のヒープ平文残留検証テスト。
//!
//! カスタムグローバルアロケータにより `dealloc` 時の解放済みメモリ内容を検査し、
//! ヒープバッファ確保後に暗号化処理がエラー終了した場合でも平文データ片が
//! ヒープ上に残留しないことを検証する。

#![cfg(feature = "alloc")]

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use fidelogic_core::{
    AES_256_GCM_SIV_NONCE_LEN, CipherSuiteId, CryptoError, KEY_LEN, VaultCipher,
    XCHACHA20_POLY1305_NONCE_LEN,
};

/// ヒープ残留検査用の固定長平文センチネル値。
const PLAINTEXT_SENTINEL: &[u8; 32] = b"FIDELOGIC_SECRET_PLAINTEXT_TEST!";

static TRACKING_ACTIVE: AtomicBool = AtomicBool::new(false);
static LEAK_DETECTED: AtomicBool = AtomicBool::new(false);
static CHECKED_DEALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);

/// 解放前のヒープブロックに平文センチネルが残っていないかを監視するテスト用アロケータ。
struct ZeroizeCheckingAllocator;

unsafe impl GlobalAlloc for ZeroizeCheckingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if TRACKING_ACTIVE.load(Ordering::SeqCst) && layout.size() >= PLAINTEXT_SENTINEL.len() {
            CHECKED_DEALLOC_COUNT.fetch_add(1, Ordering::SeqCst);
            let freed_bytes = unsafe { core::slice::from_raw_parts(ptr, layout.size()) };
            if freed_bytes
                .windows(PLAINTEXT_SENTINEL.len())
                .any(|window| window == PLAINTEXT_SENTINEL)
            {
                LEAK_DETECTED.store(true, Ordering::SeqCst);
            }
        }
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: ZeroizeCheckingAllocator = ZeroizeCheckingAllocator;

/// ヒープバッファ確保後の暗号化失敗時に平文が残留しないことを暗号スイート単位で検証する。
fn assert_no_heap_residue_on_encrypt_failure(
    suite_id: CipherSuiteId,
    key: &[u8; KEY_LEN],
    nonce: &[u8],
    plaintext: &[u8],
    aad: &[u8],
) {
    let cipher = VaultCipher::new(suite_id, key);
    let mut hook_called = false;
    let mut saw_plaintext_in_heap = false;

    LEAK_DETECTED.store(false, Ordering::SeqCst);
    CHECKED_DEALLOC_COUNT.store(0, Ordering::SeqCst);
    TRACKING_ACTIVE.store(true, Ordering::SeqCst);

    let res = cipher.encrypt_with_detached(nonce, plaintext, aad, |_, _, _, buf| {
        hook_called = true;
        saw_plaintext_in_heap = buf.len() == plaintext.len()
            && buf
                .windows(PLAINTEXT_SENTINEL.len())
                .any(|window| window == PLAINTEXT_SENTINEL);
        Err(CryptoError::AeadEncryptionFailed)
    });

    TRACKING_ACTIVE.store(false, Ordering::SeqCst);

    assert!(
        hook_called,
        "事前検証を通過してバッファ確保後の暗号化フックが呼び出されたことを確認。"
    );
    assert!(
        saw_plaintext_in_heap,
        "失敗直前のヒープバッファへ平文センチネルが書き込まれていたことを確認。"
    );
    assert_eq!(
        res,
        Err(CryptoError::AeadEncryptionFailed),
        "暗号化プリミティブ失敗エラーがそのまま返却されることを確認。"
    );
    assert!(
        CHECKED_DEALLOC_COUNT.load(Ordering::SeqCst) >= 1,
        "検査対象サイズのヒープブロックが実際に確保・解放されたことを確認。"
    );
    assert!(
        !LEAK_DETECTED.load(Ordering::SeqCst),
        "暗号化失敗時に解放されたヒープ領域へ平文が残留しないことを確認。"
    );
}

#[test]
fn test_vault_cipher_encrypt_no_heap_plaintext_residue_on_failure() {
    let key = [0x42u8; KEY_LEN];
    let aad = b"zeroize-check-aad";

    // スタック上に平文バッファを構築し、呼び出し元の平文自体はヒープに置かない。
    let mut plaintext = [0u8; 64];
    plaintext[..32].copy_from_slice(PLAINTEXT_SENTINEL);
    plaintext[32..].copy_from_slice(PLAINTEXT_SENTINEL);

    // XChaCha20-Poly1305 でバッファ確保後に暗号化が失敗する経路を検証する。
    let valid_nonce_x = [0x11u8; XCHACHA20_POLY1305_NONCE_LEN];
    assert_no_heap_residue_on_encrypt_failure(
        CipherSuiteId::XChaCha20Poly1305,
        &key,
        &valid_nonce_x,
        &plaintext,
        aad,
    );

    // AES-256-GCM-SIV でバッファ確保後に暗号化が失敗する経路を検証する。
    let valid_nonce_aes = [0x22u8; AES_256_GCM_SIV_NONCE_LEN];
    assert_no_heap_residue_on_encrypt_failure(
        CipherSuiteId::Aes256GcmSiv,
        &key,
        &valid_nonce_aes,
        &plaintext,
        aad,
    );

    // 陽性対照: ゼロ消去を行わずに解放した場合に検査アロケータがリークを検知できることを確認する。
    LEAK_DETECTED.store(false, Ordering::SeqCst);
    CHECKED_DEALLOC_COUNT.store(0, Ordering::SeqCst);
    TRACKING_ACTIVE.store(true, Ordering::SeqCst);
    {
        let leaked_vec = core::hint::black_box(PLAINTEXT_SENTINEL.to_vec());
        drop(leaked_vec);
    }
    TRACKING_ACTIVE.store(false, Ordering::SeqCst);

    assert!(
        CHECKED_DEALLOC_COUNT.load(Ordering::SeqCst) >= 1,
        "陽性対照のヒープ解放が検査されたことを確認。"
    );
    assert!(
        LEAK_DETECTED.load(Ordering::SeqCst),
        "未消去バッファの解放時に検査アロケータが平文残留を正しく検知できることを確認。"
    );
}
