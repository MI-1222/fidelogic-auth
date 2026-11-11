//! # 暗号化失敗時のヒープ平文残留検証テスト。
//!
//! カスタムグローバルアロケータにより `dealloc` 時の解放済みメモリ内容を検査し、
//! [`VaultCipher::encrypt`] がエラー終了した場合に平文データ片が
//! ヒープ上に残留しないことを検証する。

#![cfg(feature = "alloc")]

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, Ordering};

use fidelogic_core::{
    AES_256_GCM_SIV_NONCE_LEN, CipherSuiteId, CryptoError, KEY_LEN, VaultCipher,
    XCHACHA20_POLY1305_NONCE_LEN,
};

/// ヒープ残留検査用の固定長平文センチネル値。
const PLAINTEXT_SENTINEL: &[u8; 32] = b"FIDELOGIC_SECRET_PLAINTEXT_TEST!";

static TRACKING_ACTIVE: AtomicBool = AtomicBool::new(false);
static LEAK_DETECTED: AtomicBool = AtomicBool::new(false);

/// 解放前のヒープブロックに平文センチネルが残っていないかを監視するテスト用アロケータ。
struct ZeroizeCheckingAllocator;

unsafe impl GlobalAlloc for ZeroizeCheckingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if TRACKING_ACTIVE.load(Ordering::SeqCst) && layout.size() >= PLAINTEXT_SENTINEL.len() {
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

#[test]
fn test_vault_cipher_encrypt_no_heap_plaintext_residue_on_failure() {
    let key = [0x42u8; KEY_LEN];
    let aad = b"zeroize-check-aad";

    // スタック上に平文バッファを構築し、呼び出し元の平文自体はヒープに置かない。
    let mut plaintext = [0u8; 64];
    plaintext[..32].copy_from_slice(PLAINTEXT_SENTINEL);
    plaintext[32..].copy_from_slice(PLAINTEXT_SENTINEL);

    LEAK_DETECTED.store(false, Ordering::SeqCst);
    TRACKING_ACTIVE.store(true, Ordering::SeqCst);

    // XChaCha20-Poly1305 で不正ノンス長の暗号化を試行する。
    let cipher_x = VaultCipher::new(CipherSuiteId::XChaCha20Poly1305, &key);
    let invalid_nonce_x = [0x11u8; AES_256_GCM_SIV_NONCE_LEN];
    let err_x = cipher_x.encrypt(&invalid_nonce_x, &plaintext, aad);
    assert_eq!(
        err_x,
        Err(CryptoError::InvalidNonceSize),
        "XChaCha20-Poly1305 の不正ノンス長拒絶に成功。"
    );

    // AES-256-GCM-SIV で不正ノンス長の暗号化を試行する。
    let cipher_aes = VaultCipher::new(CipherSuiteId::Aes256GcmSiv, &key);
    let invalid_nonce_aes = [0x22u8; XCHACHA20_POLY1305_NONCE_LEN];
    let err_aes = cipher_aes.encrypt(&invalid_nonce_aes, &plaintext, aad);
    assert_eq!(
        err_aes,
        Err(CryptoError::InvalidNonceSize),
        "AES-256-GCM-SIV の不正ノンス長拒絶に成功。"
    );

    TRACKING_ACTIVE.store(false, Ordering::SeqCst);
    assert!(
        !LEAK_DETECTED.load(Ordering::SeqCst),
        "暗号化失敗時に解放されたヒープ領域へ平文が残留しないことを確認。"
    );
}
