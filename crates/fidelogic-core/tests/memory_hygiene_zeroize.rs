//! # 暗号化・復号の正常終了後およびエラー返却後のメモリ衛生検証テスト。
//!
//! カスタムグローバルアロケータによる解放時ヒープ全検査と、
//! インプレースバッファおよび [`VaultEngine`] のメモリ直接検査を組み合わせ、
//! 暗号化・復号・KDF・マルチスロット解錠の正常終了後およびエラー返却後において
//! 平文バッファ・DEK・中間鍵(KEK)・正準化済みリカバリーコードが
//! メモリ上に残留せず確実にゼロクリアされることを検証する。

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};

use fidelogic_core::{SecretBytes, volatile_zeroize};

/// 同時に監視可能な秘密センチネルパターンの最大数。
const MAX_WATCHED_PATTERNS: usize = 8;

/// 監視可能な単一センチネルパターンの最大バイト長。
const MAX_PATTERN_LEN: usize = 64;

/// 固定長 32 バイトの平文検査用センチネル。
const PLAINTEXT_SENTINEL: [u8; 32] = *b"FIDELOGIC_MEM_HYGIENE_PLAINTEXT!";

/// 固定長 32 バイトの DEK 検査用センチネル。
const DEK_SENTINEL: [u8; 32] = *b"FIDELOGIC_MEM_HYGIENE_DEK_BYTES!";

/// グローバルアロケータ追跡の排他制御ロック。
static ALLOC_TEST_LOCK: Mutex<()> = Mutex::new(());

/// ヒープ解放時検査の有効化フラグ。
static TRACKING_ACTIVE: AtomicBool = AtomicBool::new(false);

/// 検査対象サイズの解放回数カウンタ。
static CHECKED_DEALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);

/// 厳格全ゼロ検査の対象ポインタアドレス (`0` のとき無効)。
static EXACT_ZERO_TARGET_PTR: AtomicUsize = AtomicUsize::new(0);

/// 厳格全ゼロ検査の対象バイト長。
static EXACT_ZERO_TARGET_LEN: AtomicUsize = AtomicUsize::new(0);

/// 厳格全ゼロ検査で対象ポインタが解放された回数。
static EXACT_ZERO_HIT_COUNT: AtomicUsize = AtomicUsize::new(0);

/// 厳格全ゼロ検査で非ゼロバイトが検出されたフラグ。
static NON_ZERO_DEALLOC_DETECTED: AtomicBool = AtomicBool::new(false);

/// リークが検出されたパターン番号のビットマスク。
static LEAK_DETECTED_MASK: AtomicUsize = AtomicUsize::new(0);

/// 直近にリークが検出された解放ブロックのバイト長。
static LAST_LEAK_ALLOC_SIZE: AtomicUsize = AtomicUsize::new(0);

/// 直近にリークが検出された解放ブロック内の開始オフセット。
static LAST_LEAK_OFFSET: AtomicUsize = AtomicUsize::new(0);

/// 現在登録されている監視パターン数。
static PATTERN_COUNT: AtomicUsize = AtomicUsize::new(0);

/// 各監視パターンの長さ。
static PATTERN_LENS: [AtomicUsize; MAX_WATCHED_PATTERNS] =
    [const { AtomicUsize::new(0) }; MAX_WATCHED_PATTERNS];

/// 各監視パターンのバイト列。
static PATTERN_DATA: [[AtomicU8; MAX_PATTERN_LEN]; MAX_WATCHED_PATTERNS] =
    [const { [const { AtomicU8::new(0) }; MAX_PATTERN_LEN] }; MAX_WATCHED_PATTERNS];

/// 解放されるヒープ領域と監視センチネル群の一致判定をアロケーションなしで行う。
unsafe fn check_freed_memory_for_patterns(ptr: *const u8, len: usize) {
    let freed_bytes = unsafe { core::slice::from_raw_parts(ptr, len) };
    let count = PATTERN_COUNT
        .load(Ordering::SeqCst)
        .min(MAX_WATCHED_PATTERNS);

    for (idx, pat_len_atomic) in PATTERN_LENS.iter().enumerate().take(count) {
        let pat_len = pat_len_atomic.load(Ordering::SeqCst);
        if pat_len == 0 || pat_len > MAX_PATTERN_LEN || len < pat_len {
            continue;
        }

        let mut pat = [0u8; MAX_PATTERN_LEN];
        for (byte_idx, dst) in pat.iter_mut().enumerate().take(pat_len) {
            *dst = PATTERN_DATA[idx][byte_idx].load(Ordering::SeqCst);
        }

        if let Some(pos) = freed_bytes
            .windows(pat_len)
            .position(|window| window == &pat[..pat_len])
        {
            LAST_LEAK_ALLOC_SIZE.store(len, Ordering::SeqCst);
            LAST_LEAK_OFFSET.store(pos, Ordering::SeqCst);
            LEAK_DETECTED_MASK.fetch_or(1usize << idx, Ordering::SeqCst);
        }

        // 照合用にスタック上へ展開したパターン複製も即座にゼロクリアする。
        volatile_zeroize(&mut pat[..pat_len]);
    }
}

/// 解放直前のヒープ領域を監視し、秘密情報の残留を検知するグローバルアロケータ。
struct MemoryHygieneAllocator;

unsafe impl GlobalAlloc for MemoryHygieneAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if TRACKING_ACTIVE.load(Ordering::SeqCst) && layout.size() >= 8 {
            CHECKED_DEALLOC_COUNT.fetch_add(1, Ordering::SeqCst);
            unsafe { check_freed_memory_for_patterns(ptr, layout.size()) };
        }
        let target_ptr = EXACT_ZERO_TARGET_PTR.load(Ordering::SeqCst);
        if target_ptr != 0 && ptr as usize == target_ptr {
            EXACT_ZERO_HIT_COUNT.fetch_add(1, Ordering::SeqCst);
            let target_len = EXACT_ZERO_TARGET_LEN
                .load(Ordering::SeqCst)
                .min(layout.size());
            let freed_bytes = unsafe { core::slice::from_raw_parts(ptr, target_len) };
            if freed_bytes.iter().any(|&b| b != 0) {
                NON_ZERO_DEALLOC_DETECTED.store(true, Ordering::SeqCst);
            }
        }
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: MemoryHygieneAllocator = MemoryHygieneAllocator;

/// 監視パターンをロックフリーテーブルへ登録し、指定クロージャ実行中のヒープ解放残留を検査する。
fn run_with_heap_leak_check<F, R>(patterns: &[&[u8]], min_expected_deallocs: usize, f: F) -> R
where
    F: FnOnce() -> R,
{
    assert!(
        patterns.len() <= MAX_WATCHED_PATTERNS,
        "監視パターン数が上限を超過。"
    );

    let _guard = ALLOC_TEST_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());

    for (idx, pat) in patterns.iter().enumerate() {
        assert!(
            !pat.is_empty() && pat.len() <= MAX_PATTERN_LEN,
            "監視パターン長が許容範囲外。"
        );
        PATTERN_LENS[idx].store(pat.len(), Ordering::SeqCst);
        for (byte_idx, &byte) in pat.iter().enumerate() {
            PATTERN_DATA[idx][byte_idx].store(byte, Ordering::SeqCst);
        }
    }
    for len_slot in PATTERN_LENS.iter().skip(patterns.len()) {
        len_slot.store(0, Ordering::SeqCst);
    }
    PATTERN_COUNT.store(patterns.len(), Ordering::SeqCst);
    CHECKED_DEALLOC_COUNT.store(0, Ordering::SeqCst);
    LEAK_DETECTED_MASK.store(0, Ordering::SeqCst);
    LAST_LEAK_ALLOC_SIZE.store(0, Ordering::SeqCst);
    LAST_LEAK_OFFSET.store(0, Ordering::SeqCst);

    TRACKING_ACTIVE.store(true, Ordering::SeqCst);
    let result = f();
    TRACKING_ACTIVE.store(false, Ordering::SeqCst);

    let dealloc_count = CHECKED_DEALLOC_COUNT.load(Ordering::SeqCst);
    let leak_mask = LEAK_DETECTED_MASK.load(Ordering::SeqCst);

    // テスト終了後に監視テーブル自体もゼロクリアする。
    for row in &PATTERN_DATA {
        for cell in row {
            cell.store(0, Ordering::SeqCst);
        }
    }
    PATTERN_COUNT.store(0, Ordering::SeqCst);

    assert!(
        dealloc_count >= min_expected_deallocs,
        "期待されるヒープ解放回数に未達: observed={dealloc_count}, expected>={min_expected_deallocs}"
    );
    let leak_size = LAST_LEAK_ALLOC_SIZE.load(Ordering::SeqCst);
    let leak_offset = LAST_LEAK_OFFSET.load(Ordering::SeqCst);
    assert_eq!(
        leak_mask, 0,
        "解放済みヒープ領域に未消去の秘密情報パターンが残留: mask={leak_mask:#b}, len={leak_size}, offset={leak_offset}"
    );

    result
}

/// 指定されたポインタ・長さのヒープ領域が解放時に 100% ゼロ埋め (`0x00`) されていることを厳格検証する。
fn assert_exact_zero_on_dealloc<T, F>(make_boxed: F)
where
    F: FnOnce() -> (T, usize, usize),
{
    let _guard = ALLOC_TEST_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());

    let (handle, ptr, len) = make_boxed();
    assert_ne!(ptr, 0, "対象ポインタが非NULLであることを確認。");

    EXACT_ZERO_HIT_COUNT.store(0, Ordering::SeqCst);
    NON_ZERO_DEALLOC_DETECTED.store(false, Ordering::SeqCst);
    EXACT_ZERO_TARGET_LEN.store(len, Ordering::SeqCst);
    EXACT_ZERO_TARGET_PTR.store(ptr, Ordering::SeqCst);

    drop(handle);

    EXACT_ZERO_TARGET_PTR.store(0, Ordering::SeqCst);
    EXACT_ZERO_TARGET_LEN.store(0, Ordering::SeqCst);

    let hits = EXACT_ZERO_HIT_COUNT.load(Ordering::SeqCst);
    let non_zero = NON_ZERO_DEALLOC_DETECTED.load(Ordering::SeqCst);

    assert_eq!(
        hits, 1,
        "対象ヒープブロックの解放が正確に 1 回観測されたことを確認。"
    );
    assert!(
        !non_zero,
        "解放された対象ヒープ領域に非ゼロバイトが残存しています。"
    );
}

/// 陽性対照用: リーク検知ビットマスクを返却するヘルパー。
fn measure_leak_mask_for_unzeroized<F>(patterns: &[&[u8]], f: F) -> (usize, usize)
where
    F: FnOnce(),
{
    let _guard = ALLOC_TEST_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());

    for (idx, pat) in patterns.iter().enumerate() {
        PATTERN_LENS[idx].store(pat.len(), Ordering::SeqCst);
        for (byte_idx, &byte) in pat.iter().enumerate() {
            PATTERN_DATA[idx][byte_idx].store(byte, Ordering::SeqCst);
        }
    }
    PATTERN_COUNT.store(patterns.len(), Ordering::SeqCst);
    CHECKED_DEALLOC_COUNT.store(0, Ordering::SeqCst);
    LEAK_DETECTED_MASK.store(0, Ordering::SeqCst);

    TRACKING_ACTIVE.store(true, Ordering::SeqCst);
    f();
    TRACKING_ACTIVE.store(false, Ordering::SeqCst);

    let dealloc_count = CHECKED_DEALLOC_COUNT.load(Ordering::SeqCst);
    let leak_mask = LEAK_DETECTED_MASK.load(Ordering::SeqCst);

    for row in &PATTERN_DATA {
        for cell in row {
            cell.store(0, Ordering::SeqCst);
        }
    }
    PATTERN_COUNT.store(0, Ordering::SeqCst);

    (dealloc_count, leak_mask)
}

#[test]
fn test_positive_control_allocator_detects_unzeroized_heap_secrets() {
    let (deallocs, leak_mask) =
        measure_leak_mask_for_unzeroized(&[&PLAINTEXT_SENTINEL, &DEK_SENTINEL], || {
            let unzeroized_pt = core::hint::black_box(PLAINTEXT_SENTINEL.to_vec());
            drop(unzeroized_pt);
            let unzeroized_dek = core::hint::black_box(Box::new(DEK_SENTINEL));
            drop(unzeroized_dek);
        });

    assert!(
        deallocs >= 2,
        "陽性対照のヒープ解放が監視されたことを確認。"
    );
    assert_eq!(
        leak_mask, 0b11,
        "ゼロ消去しないヒープ解放では両パターンの残留を確実に検知できることを確認。"
    );
}

#[test]
fn test_secret_bytes_and_volatile_zeroize_hygiene() {
    let mut stack_buf = PLAINTEXT_SENTINEL;
    volatile_zeroize(&mut stack_buf);
    assert_eq!(
        stack_buf, [0u8; 32],
        "volatile_zeroize 後のスタックバッファが完全にゼロクリアされることを確認。"
    );

    run_with_heap_leak_check(&[&DEK_SENTINEL], 1, || {
        let boxed_secret = core::hint::black_box(Box::new(SecretBytes::new(DEK_SENTINEL)));
        assert_eq!(boxed_secret.as_bytes(), &DEK_SENTINEL);
        drop(boxed_secret);
    });

    // Box<SecretBytes<32>> の全 32 バイトが Drop 時に 0x00 へ消去されることを厳格検証する。
    assert_exact_zero_on_dealloc(|| {
        let boxed_secret = core::hint::black_box(Box::new(SecretBytes::new(DEK_SENTINEL)));
        assert_eq!(boxed_secret.as_bytes(), &DEK_SENTINEL);
        let ptr = (&*boxed_secret as *const SecretBytes<32>).cast::<u8>() as usize;
        (boxed_secret, ptr, 32)
    });
}

#[cfg(feature = "alloc")]
#[test]
fn test_secret_vec_hygiene_on_clear_and_drop() {
    use fidelogic_core::SecretVec;

    run_with_heap_leak_check(&[&PLAINTEXT_SENTINEL], 2, || {
        let mut svec_clear = SecretVec::from_slice(&PLAINTEXT_SENTINEL);
        svec_clear.clear();
        drop(svec_clear);

        let svec_drop = SecretVec::from_slice(&PLAINTEXT_SENTINEL);
        assert_eq!(svec_drop.as_slice(), &PLAINTEXT_SENTINEL);
        drop(svec_drop);
    });

    assert_exact_zero_on_dealloc(|| {
        let svec_drop = SecretVec::from_slice(&PLAINTEXT_SENTINEL);
        assert_eq!(svec_drop.as_slice(), &PLAINTEXT_SENTINEL);
        let ptr = svec_drop.as_slice().as_ptr() as usize;
        let len = svec_drop.capacity();
        (svec_drop, ptr, len)
    });
}

#[cfg(feature = "alloc")]
#[test]
fn test_opaque_string_memory_hygiene_success_and_error() {
    use fidelogic_core::{
        PrecisError, PrecisProfile, enforce_opaque_string_cps, opaque_string, opaque_string_secret,
    };

    // テスト用パスワード平文 (ASCII + 非 ASCII 空白 U+00A0 + 結合文字 A + U+0308)。
    let password_raw = "S3cr3tP@ss\u{00A0}W0rd\u{0020}A\u{0308}#2026";
    let password_canonical = "S3cr3tP@ss W0rd Ä#2026";
    let bad_password = "S3cr3tP@ss\u{00A0}\0Bad#2026";

    // 監視対象パターン:
    // 1. 平文パスワードの UTF-8 部分文字列
    // 2. 正準化後のパスワード UTF-8 部分文字列
    // 3. コードポイント列の 32-bit ワード列 (リトルエンディアンバイト列)
    let pattern_pw_raw = b"S3cr3tP@ss";
    let pattern_pw_canonical = b"S3cr3tP@ss W0rd";
    let pattern_bad = b"Bad#2026";

    // "S3cr" のコードポイント列バイトパターン ([83, 51, 99, 114])。
    let cps_slice = [83u32, 51u32, 99u32, 114u32];
    let cps_bytes = unsafe { core::slice::from_raw_parts(cps_slice.as_ptr().cast::<u8>(), 16) };

    // 1. opaque_string_secret 正常終了後:
    // 中間 Vec<u32> (cps, mapped, normalized) および戻り値 SecretVec の Drop 後に
    // 平文およびコードポイント列がヒープ上に残留しないことを検証。
    run_with_heap_leak_check(
        &[pattern_pw_raw, pattern_pw_canonical, cps_bytes],
        3,
        || {
            let secret =
                opaque_string_secret(password_raw).expect("opaque_string_secret 正常系に成功。");
            assert_eq!(secret.as_slice(), password_canonical.as_bytes());
            drop(secret);
        },
    );

    // 2. opaque_string_secret エラー返却後:
    // 禁止文字混入による失敗時、中間バッファが確実にゼロ消去されて解放されることを検証。
    run_with_heap_leak_check(&[pattern_pw_raw, pattern_bad, cps_bytes], 1, || {
        let err = opaque_string_secret(bad_password)
            .expect_err("禁止コードポイントにより失敗することを検証。");
        assert_eq!(err, PrecisError::DisallowedCodePoint(0x0000));
    });

    // 3. opaque_string (String 返却 API) の中間バッファ衛生:
    // 中間 Vec<u32> (cps, mapped, normalized) が確実にゼロ消去されて解放されることを検証。
    run_with_heap_leak_check(&[cps_bytes], 2, || {
        let s = opaque_string(password_raw).expect("opaque_string 正常系に成功。");
        assert_eq!(s, password_canonical);
        // 注: s (String) 自体は標準型のため Drop でゼロ消去されないが、
        // 中間コードポイント Vec<u32> は完全にゼロ消去されることを cps_bytes で検証。
        drop(s);
    });

    // 4. enforce_opaque_string_cps エラー返却時のメモリ衛生:
    // 禁止文字が含まれるコードポイント列の正規化途中で失敗した場合でも、
    // 中間 Vec<u32> がゼロクリアされて解放されることを検証。
    let bad_cps: Vec<u32> = bad_password.chars().map(|c| c as u32).collect();
    run_with_heap_leak_check(&[cps_bytes], 1, || {
        let err = enforce_opaque_string_cps(&bad_cps)
            .expect_err("enforce_opaque_string_cps 失敗を検証。");
        assert_eq!(err, PrecisError::DisallowedCodePoint(0x0000));
    });

    // 5. PrecisProfile::OpaqueString.enforce_str_secret のメモリ衛生。
    run_with_heap_leak_check(
        &[pattern_pw_raw, pattern_pw_canonical, cps_bytes],
        3,
        || {
            let prof = PrecisProfile::OpaqueString;
            let secret = prof
                .enforce_str_secret(password_raw)
                .expect("enforce_str_secret 正常系に成功。");
            assert_eq!(secret.as_slice(), password_canonical.as_bytes());
            drop(secret);
        },
    );
}

#[cfg(feature = "alloc")]
#[test]
fn test_username_case_mapped_memory_hygiene_success_and_error() {
    use fidelogic_core::{PrecisError, enforce_username_case_mapped_cps, username_case_mapped};

    let user_raw = "Alice\u{0020}User#2026";
    let bad_cps: [u32; 4] = [b'A' as u32, 0x0020, b'B' as u32, 0x0000];
    let cps_slice = [b'A' as u32, 0x0020, b'B' as u32];
    let cps_bytes = unsafe { core::slice::from_raw_parts(cps_slice.as_ptr().cast::<u8>(), 12) };

    // 1. username_case_mapped 禁止文字 (0x0020 空白) によるエラー時:
    // 中間 Vec<u32> (cps, folded, normalized) が Zeroizing により確実にゼロ消去されて解放されることを検証。
    run_with_heap_leak_check(&[cps_bytes], 1, || {
        let err =
            username_case_mapped(user_raw).expect_err("空白文字が含まれるため失敗することを検証。");
        assert_eq!(err, PrecisError::DisallowedCodePoint(0x0020));
    });

    // 2. enforce_username_case_mapped_cps エラー返却時のメモリ衛生:
    run_with_heap_leak_check(&[cps_bytes], 1, || {
        let err = enforce_username_case_mapped_cps(&bad_cps)
            .expect_err("enforce_username_case_mapped_cps 失敗を検証。");
        assert_eq!(err, PrecisError::DisallowedCodePoint(0x0020));
    });
}

#[cfg(feature = "profile-lite")]
#[test]
fn test_x25519_dh_memory_hygiene_success_and_error() {
    use fidelogic_core::{
        CryptoError, X25519PublicKey, x25519_basepoint_mul, x25519_diffie_hellman,
    };

    let alice_secret_raw = *b"FIDELOGIC_X25519_ALICE_PRIV_KEY!";
    let bob_secret_raw = *b"FIDELOGIC_X25519_BOB_PRIV_KEY!!!";
    let bob_secret = SecretBytes::new(bob_secret_raw);
    let bob_pub = x25519_basepoint_mul(&bob_secret);

    let expected_shared = {
        let alice_secret = SecretBytes::new(alice_secret_raw);
        *x25519_diffie_hellman(&alice_secret, &bob_pub)
            .expect("X25519 DH に成功。")
            .as_bytes()
    };

    // 正常終了後: Box<SecretBytes> および Box<X25519SharedSecret> の破棄時に鍵と共有秘密が残留しない。
    run_with_heap_leak_check(&[&alice_secret_raw, &expected_shared], 2, || {
        let alice_secret = core::hint::black_box(Box::new(SecretBytes::new(alice_secret_raw)));
        let shared = core::hint::black_box(Box::new(
            x25519_diffie_hellman(&alice_secret, &bob_pub).expect("正常な X25519 DH に成功。"),
        ));
        assert_eq!(shared.as_bytes(), &expected_shared);
        drop(shared);
        drop(alice_secret);
    });

    // エラー返却後: 低位数点(全ゼロ公開鍵)による失敗時も秘密鍵が残留しない。
    run_with_heap_leak_check(&[&alice_secret_raw], 1, || {
        let alice_secret = core::hint::black_box(Box::new(SecretBytes::new(alice_secret_raw)));
        let low_order_pub = X25519PublicKey::new([0u8; 32]);
        let err = x25519_diffie_hellman(&alice_secret, &low_order_pub).err();
        assert_eq!(err, Some(CryptoError::InvalidParameter));
        drop(alice_secret);
    });
}

#[cfg(feature = "memlock")]
#[test]
fn test_locked_buffer_memory_hygiene_on_zeroize_and_drop() {
    use fidelogic_core::LockedBuffer;
    use zeroize::Zeroize;

    run_with_heap_leak_check(&[&DEK_SENTINEL], 0, || {
        let mut buf1 = LockedBuffer::new(DEK_SENTINEL);
        assert_eq!(buf1.as_bytes(), &DEK_SENTINEL);
        buf1.zeroize();
        assert_eq!(
            buf1.as_bytes(),
            &[0u8; 32],
            "LockedBuffer::zeroize 後に内部メモリが全ゼロ化されることを確認。"
        );
        drop(buf1);

        let buf2 = LockedBuffer::new(DEK_SENTINEL);
        assert_eq!(buf2.as_bytes(), &DEK_SENTINEL);
        drop(buf2);
    });
}

#[cfg(all(feature = "alloc", feature = "profile-vault"))]
mod vault_memory_hygiene_tests {
    use super::*;
    use fidelogic_core::envelope::{SLOT_ID_PRF, VaultState};
    use fidelogic_core::kdf::{
        Argon2Params, HKDF_SHA256_MAX_OUTPUT_LEN, hkdf_sha256_derive, hkdf_sha256_derive_32,
        hkdf_sha256_derive_vec,
    };
    use fidelogic_core::slots::{
        SLOT0_NONCE_LEN, SLOT0_SALT_LEN, SLOT1_NONCE_LEN, SLOT1_SALT_LEN, SLOT2_NONCE_LEN,
        SLOT2_SALT_LEN, SlotCredential, normalize_recovery_code, unwrap_dek_slot0_with_secret,
        unwrap_dek_slot1, unwrap_dek_slot2_code, wrap_dek_slot0, wrap_dek_slot0_with_secret,
        wrap_dek_slot1, wrap_dek_slot2_code,
    };
    use fidelogic_core::tlv::{EntryPayload, TlvRecord, Vault, VaultHeader};
    use fidelogic_core::{
        AES_256_GCM_SIV_NONCE_LEN, CipherSuiteId, CryptoError, KEY_LEN, SlotKind, SlotStatus,
        TAG_LEN, VaultCipher, VaultEngine, VaultError, XCHACHA20_POLY1305_NONCE_LEN,
    };

    /// 固定長 32 バイトの鍵検査用センチネル。
    const KEY_SENTINEL: [u8; 32] = *b"FIDELOGIC_MEM_HYGIENE_CIPHERKEY!";

    /// テスト用 64 バイト平文(センチネル 2 連)を構築する。
    fn make_plaintext_64() -> [u8; 64] {
        let mut pt = [0u8; 64];
        pt[..32].copy_from_slice(&PLAINTEXT_SENTINEL);
        pt[32..].copy_from_slice(&PLAINTEXT_SENTINEL);
        pt
    }

    #[test]
    fn test_cipher_encrypt_memory_hygiene_success_and_error() {
        let aad = b"fidelogic-cipher-encrypt-aad";
        let plaintext = make_plaintext_64();

        for (suite, nonce) in [
            (
                CipherSuiteId::XChaCha20Poly1305,
                &[0x11u8; XCHACHA20_POLY1305_NONCE_LEN][..],
            ),
            (
                CipherSuiteId::Aes256GcmSiv,
                &[0x22u8; AES_256_GCM_SIV_NONCE_LEN][..],
            ),
        ] {
            // 1. 正常終了後 (インプレース): 平文バッファが暗号文で上書きされ、VaultCipher 破棄時に鍵が残らない。
            let mut in_place_buf = plaintext;
            run_with_heap_leak_check(&[&PLAINTEXT_SENTINEL, &KEY_SENTINEL], 1, || {
                let cipher =
                    core::hint::black_box(Box::new(VaultCipher::new(suite, &KEY_SENTINEL)));
                let tag = cipher
                    .encrypt_in_place_detached(nonce, aad, &mut in_place_buf)
                    .expect("インプレース暗号化に成功。");
                assert_ne!(tag, [0u8; TAG_LEN]);
                assert!(
                    !in_place_buf
                        .windows(PLAINTEXT_SENTINEL.len())
                        .any(|w| w == PLAINTEXT_SENTINEL),
                    "暗号化成功後のインプレースバッファに平文センチネルが残存しないことを確認。"
                );
                drop(cipher);
            });

            // 2. 正常終了後 (alloc encrypt): 一時バッファ・出力暗号文・VaultCipher 破棄時に平文や鍵が残留しない。
            let ct_with_tag =
                run_with_heap_leak_check(&[&PLAINTEXT_SENTINEL, &KEY_SENTINEL], 1, || {
                    let cipher =
                        core::hint::black_box(Box::new(VaultCipher::new(suite, &KEY_SENTINEL)));
                    let ct = cipher
                        .encrypt(nonce, &plaintext, aad)
                        .expect("alloc 暗号化に成功。");
                    assert!(
                        !ct.windows(PLAINTEXT_SENTINEL.len())
                            .any(|w| w == PLAINTEXT_SENTINEL),
                        "出力暗号文に平文が含まれないことを確認。"
                    );
                    drop(cipher);
                    ct
                });
            assert_eq!(ct_with_tag.len(), plaintext.len() + TAG_LEN);

            // 3. 可変サイズ平文 (1〜1024B) でも再確保等で平文が残留しない。
            for extra_len in [1usize, 15, 16, 64, 256, 1024] {
                let mut sized_pt = vec![0x7Au8; PLAINTEXT_SENTINEL.len() + extra_len];
                sized_pt[..PLAINTEXT_SENTINEL.len()].copy_from_slice(&PLAINTEXT_SENTINEL);
                run_with_heap_leak_check(&[&PLAINTEXT_SENTINEL, &KEY_SENTINEL], 1, || {
                    let cipher =
                        core::hint::black_box(Box::new(VaultCipher::new(suite, &KEY_SENTINEL)));
                    let ct = cipher
                        .encrypt(nonce, &sized_pt, aad)
                        .expect("可変長暗号化に成功。");
                    assert!(
                        !ct.windows(PLAINTEXT_SENTINEL.len())
                            .any(|w| w == PLAINTEXT_SENTINEL)
                    );
                    drop(cipher);
                });
            }

            // 4. エラー返却後 (暗号化失敗経路): ヒープバッファおよび鍵が即座にゼロクリアされる。
            run_with_heap_leak_check(&[&PLAINTEXT_SENTINEL, &KEY_SENTINEL], 2, || {
                let cipher =
                    core::hint::black_box(Box::new(VaultCipher::new(suite, &KEY_SENTINEL)));
                let mut saw_plaintext_in_heap = false;
                let err = cipher.encrypt_with_detached(nonce, &plaintext, aad, |_, _, _, buf| {
                    saw_plaintext_in_heap = buf == plaintext;
                    // フック側ではゼロ消去を行わずにエラー返却し、VaultCipher 側の自動ゼロクリアを検証する。
                    Err(CryptoError::AeadEncryptionFailed)
                });
                assert!(saw_plaintext_in_heap);
                assert_eq!(err, Err(CryptoError::AeadEncryptionFailed));
                drop(cipher);
            });

            // 5. VaultCipher 全体フットプリント(列挙型パディング含む)の解放時 100% ゼロ化を厳格検証する。
            assert_exact_zero_on_dealloc(|| {
                let cipher =
                    core::hint::black_box(Box::new(VaultCipher::new(suite, &KEY_SENTINEL)));
                let ptr = (&*cipher as *const VaultCipher) as usize;
                let len = core::mem::size_of::<VaultCipher>();
                (cipher, ptr, len)
            });
        }
    }

    #[test]
    fn test_cipher_decrypt_memory_hygiene_success_and_error() {
        let aad = b"fidelogic-cipher-decrypt-aad";
        let wrong_aad = b"fidelogic-cipher-wrong-epoch";
        let wrong_key = [0x99u8; KEY_LEN];
        let plaintext = make_plaintext_64();

        for (suite, nonce) in [
            (
                CipherSuiteId::XChaCha20Poly1305,
                &[0x31u8; XCHACHA20_POLY1305_NONCE_LEN][..],
            ),
            (
                CipherSuiteId::Aes256GcmSiv,
                &[0x41u8; AES_256_GCM_SIV_NONCE_LEN][..],
            ),
        ] {
            let cipher = VaultCipher::new(suite, &KEY_SENTINEL);
            let ct_with_tag = cipher
                .encrypt(nonce, &plaintext, aad)
                .expect("テスト用暗号文生成に成功。");
            let mut in_place_ct = plaintext;
            let tag = cipher
                .encrypt_in_place_detached(nonce, aad, &mut in_place_ct)
                .expect("テスト用分離暗号文生成に成功。");

            // 1. 正常終了後 (alloc decrypt): SecretVec 破棄時に復号済み平文が完全にゼロ消去される。
            run_with_heap_leak_check(&[&PLAINTEXT_SENTINEL, &KEY_SENTINEL], 2, || {
                let boxed_cipher =
                    core::hint::black_box(Box::new(VaultCipher::new(suite, &KEY_SENTINEL)));
                let pt_secret = boxed_cipher
                    .decrypt(nonce, &ct_with_tag, aad)
                    .expect("正常復号に成功。");
                assert_eq!(pt_secret.as_slice(), &plaintext);
                drop(pt_secret);
                drop(boxed_cipher);
            });

            // 2. 正常終了後 (インプレース復号): 復号後に volatile_zeroize すると全ゼロになる。
            let mut dec_buf = in_place_ct;
            cipher
                .decrypt_in_place_detached_tag(nonce, aad, &mut dec_buf, &tag)
                .expect("インプレース正常復号に成功。");
            assert_eq!(dec_buf, plaintext);
            volatile_zeroize(&mut dec_buf);
            assert_eq!(dec_buf, [0u8; 64]);

            // 3. エラー返却後 (インプレース復号): タグ改ざん・暗号文改ざん・AAD不一致・鍵不一致のすべてで即座にゼロクリアされる。
            let mut bad_tag = tag;
            bad_tag[0] ^= 0xff;
            let mut buf_bad_tag = in_place_ct;
            assert_eq!(
                cipher.decrypt_in_place_detached(nonce, aad, &mut buf_bad_tag, &bad_tag),
                Err(CryptoError::AeadDecryptionFailed)
            );
            assert_eq!(
                buf_bad_tag, [0u8; 64],
                "タグ改ざん時のインプレースバッファが即座にゼロクリアされることを確認。"
            );

            let mut tampered_ct = in_place_ct;
            tampered_ct[0] ^= 0x01;
            assert_eq!(
                cipher.decrypt_in_place_detached_tag(nonce, aad, &mut tampered_ct, &tag),
                Err(CryptoError::AeadDecryptionFailed)
            );
            assert_eq!(
                tampered_ct, [0u8; 64],
                "暗号文改ざん時のインプレースバッファが即座にゼロクリアされることを確認。"
            );

            let mut buf_wrong_aad = in_place_ct;
            assert_eq!(
                cipher.decrypt_in_place_detached_tag(nonce, wrong_aad, &mut buf_wrong_aad, &tag),
                Err(CryptoError::AeadDecryptionFailed)
            );
            assert_eq!(
                buf_wrong_aad, [0u8; 64],
                "AAD 不一致(世代巻き戻し等)時のインプレースバッファが即座にゼロクリアされることを確認。"
            );

            let wrong_cipher = VaultCipher::new(suite, &wrong_key);
            let mut buf_wrong_key = in_place_ct;
            assert_eq!(
                wrong_cipher.decrypt_in_place_detached_tag(nonce, aad, &mut buf_wrong_key, &tag),
                Err(CryptoError::AeadDecryptionFailed)
            );
            assert_eq!(
                buf_wrong_key, [0u8; 64],
                "誤鍵での復号失敗時のインプレースバッファが即座にゼロクリアされることを確認。"
            );

            // 4. エラー返却後 (alloc decrypt): 復号失敗時に候補バッファおよび鍵がヒープに残留しない。
            let mut ct_bad_tag = ct_with_tag.clone();
            let last_idx = ct_bad_tag.len() - 1;
            ct_bad_tag[last_idx] ^= 0xff;

            run_with_heap_leak_check(&[&PLAINTEXT_SENTINEL, &KEY_SENTINEL], 2, || {
                let boxed_cipher =
                    core::hint::black_box(Box::new(VaultCipher::new(suite, &KEY_SENTINEL)));
                assert_eq!(
                    boxed_cipher.decrypt(nonce, &ct_bad_tag, aad).err(),
                    Some(CryptoError::AeadDecryptionFailed)
                );
                assert_eq!(
                    boxed_cipher.decrypt(nonce, &ct_with_tag, wrong_aad).err(),
                    Some(CryptoError::AeadDecryptionFailed)
                );
                drop(boxed_cipher);
            });
        }
    }

    #[test]
    fn test_kdf_memory_hygiene_success_and_error() {
        let params = Argon2Params::fast_test();
        let password = b"FIDELOGIC_KDF_PASSWORD_SECRET_32";
        let salt = b"fidelogic-kdf-salt-16";
        let pepper = b"FIDELOGIC_KDF_PEPPER_SECRET_KEY!";

        let expected_argon2_key = *params
            .derive_key_32_with_secret(password, salt, pepper)
            .expect("期待 Argon2id 鍵導出に成功。")
            .as_bytes();

        let hkdf_salt = b"fidelogic-hkdf-salt-32-bytes-pad";
        let hkdf_ikm = b"FIDELOGIC_HKDF_IKM_SECRET_32BYTE";
        let hkdf_info = b"fidelogic-hkdf-info";
        let expected_hkdf_key = *hkdf_sha256_derive_32(hkdf_salt, hkdf_ikm, hkdf_info)
            .expect("期待 HKDF 鍵導出に成功。")
            .as_bytes();

        // 1. Argon2id 正常終了後: SecretVec / Box<SecretBytes> / Argon2 作業ブロックのすべてに鍵・パスワードが残留しない。
        run_with_heap_leak_check(&[&expected_argon2_key, password, pepper], 3, || {
            let derived_vec = params
                .derive_key_vec_with_secret(password, salt, pepper)
                .expect("SecretVec 鍵導出に成功。");
            assert_eq!(derived_vec.as_slice(), &expected_argon2_key);
            drop(derived_vec);

            let derived_32 = core::hint::black_box(Box::new(
                params
                    .derive_key_32_with_secret(password, salt, pepper)
                    .expect("SecretBytes 鍵導出に成功。"),
            ));
            assert_eq!(derived_32.as_bytes(), &expected_argon2_key);
            drop(derived_32);
        });

        // 2. Argon2id エラー返却後: 出力バッファおよび失敗経路ヒープに非ゼロデータが残らない。
        let mut argon2_out = [0xAAu8; 32];
        assert_eq!(
            params.derive_key_with_secret(password, b"short", pepper, &mut argon2_out),
            Err(CryptoError::KeyDerivationFailed)
        );
        assert_eq!(argon2_out, [0u8; 32]);

        run_with_heap_leak_check(&[&expected_argon2_key, password, pepper], 1, || {
            assert_eq!(
                params
                    .derive_key_vec_with_secret(password, b"short", pepper)
                    .err(),
                Some(CryptoError::KeyDerivationFailed)
            );
        });

        // 3. HKDF-SHA256 正常終了後およびエラー返却後: 中間 PRK・出力鍵が残留しない。
        run_with_heap_leak_check(&[&expected_hkdf_key, hkdf_ikm], 2, || {
            let hkdf_vec = hkdf_sha256_derive_vec(hkdf_salt, hkdf_ikm, hkdf_info, 32)
                .expect("HKDF SecretVec 導出に成功。");
            assert_eq!(hkdf_vec.as_slice(), &expected_hkdf_key);
            drop(hkdf_vec);

            let hkdf_32 = core::hint::black_box(Box::new(
                hkdf_sha256_derive_32(hkdf_salt, hkdf_ikm, hkdf_info)
                    .expect("HKDF SecretBytes 導出に成功。"),
            ));
            assert_eq!(hkdf_32.as_bytes(), &expected_hkdf_key);
            drop(hkdf_32);
        });

        let mut hkdf_out = [0u8; 32];
        hkdf_sha256_derive(hkdf_salt, hkdf_ikm, hkdf_info, &mut hkdf_out)
            .expect("HKDF スタック導出に成功。");
        assert_eq!(hkdf_out, expected_hkdf_key);
        volatile_zeroize(&mut hkdf_out);
        assert_eq!(hkdf_out, [0u8; 32]);

        let mut oversized_hkdf = [0x55u8; HKDF_SHA256_MAX_OUTPUT_LEN + 1];
        assert_eq!(
            hkdf_sha256_derive(hkdf_salt, hkdf_ikm, hkdf_info, &mut oversized_hkdf),
            Err(CryptoError::InvalidKeySize)
        );
        assert!(oversized_hkdf.iter().all(|&b| b == 0));
    }

    #[test]
    fn test_slots_wrap_unwrap_memory_hygiene_success_and_error() {
        let params = Argon2Params::fast_test();
        let dek = SecretBytes::new(DEK_SENTINEL);
        let password = b"FIDELOGIC_SLOT0_MASTER_PASSWORD!";
        let pepper = b"FIDELOGIC_SLOT0_PEPPER_SECRET!!!";
        let slot0_salt: [u8; SLOT0_SALT_LEN] = *b"slot0-salt-16byt";
        let slot0_nonce: [u8; SLOT0_NONCE_LEN] = *b"slot0-xchacha20-nonce-24";

        let prf_secret = b"FIDELOGIC_SLOT1_PRF_SECRET_32BYT";
        let slot1_salt: [u8; SLOT1_SALT_LEN] = *b"slot1-hkdf-salt-32-bytes-0000001";
        let slot1_nonce: [u8; SLOT1_NONCE_LEN] = *b"slot1-xchacha20-nonce-24";

        let recovery_code_formatted = b"abcd-efgh-ijkl-mnop-qrst-uvwx-yz12";
        let recovery_code_canonical = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ12";
        let slot2_salt: [u8; SLOT2_SALT_LEN] = *b"slot2-hkdf-salt-32-bytes-0000002";
        let slot2_nonce: [u8; SLOT2_NONCE_LEN] = *b"slot2-xchacha20-nonce-24";

        let vault_aad = b"FVAU\x01\x01\x00\x00\x00\x00\x00\x00\x00\x01";
        let wrong_aad = b"FVAU\x01\x01\x00\x00\x00\x00\x00\x00\x00\x00";

        // 中間 KEK 期待値を事前計算し、ヒープ監視パターンに含める。
        let kek0 = *params
            .derive_key_32_with_secret(password, &slot0_salt, pepper)
            .expect("Slot 0 KEK 事前計算に成功。")
            .as_bytes();
        let kek1 = *hkdf_sha256_derive_32(
            &slot1_salt,
            prf_secret,
            b"fidelogic-slot1-hkdf-sha256-kek-v1",
        )
        .expect("Slot 1 KEK 事前計算に成功。")
        .as_bytes();
        let kek2 = *hkdf_sha256_derive_32(
            &slot2_salt,
            recovery_code_canonical,
            b"fidelogic-slot2-recovery-hkdf-sha256-kek-v1",
        )
        .expect("Slot 2 KEK 事前計算に成功。")
        .as_bytes();

        // 1. Slot 0 ラップ/アンラップの正常終了とエラー返却時メモリ衛生。
        let slot0_entry =
            run_with_heap_leak_check(&[&DEK_SENTINEL, &kek0, password, pepper], 2, || {
                let entry = wrap_dek_slot0_with_secret(
                    &dek,
                    password,
                    &slot0_salt,
                    &slot0_nonce,
                    &params,
                    pepper,
                    vault_aad,
                )
                .expect("Slot 0 DEK ラップに成功。");
                let unwrapped = core::hint::black_box(Box::new(
                    unwrap_dek_slot0_with_secret(&entry, password, pepper, vault_aad)
                        .expect("Slot 0 DEK アンラップに成功。"),
                ));
                assert_eq!(unwrapped.as_bytes(), &DEK_SENTINEL);
                drop(unwrapped);
                entry
            });

        run_with_heap_leak_check(&[&DEK_SENTINEL, &kek0, password, pepper], 2, || {
            assert_eq!(
                unwrap_dek_slot0_with_secret(&slot0_entry, b"wrong-password", pepper, vault_aad)
                    .err(),
                Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
            );
            assert_eq!(
                unwrap_dek_slot0_with_secret(&slot0_entry, password, pepper, wrong_aad).err(),
                Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
            );
        });

        // 2. Slot 1 ラップ/アンラップの正常終了とエラー返却時メモリ衛生。
        let slot1_entry = run_with_heap_leak_check(&[&DEK_SENTINEL, &kek1, prf_secret], 2, || {
            let entry = wrap_dek_slot1(&dek, prf_secret, &slot1_salt, &slot1_nonce, vault_aad)
                .expect("Slot 1 DEK ラップに成功。");
            let unwrapped = core::hint::black_box(Box::new(
                unwrap_dek_slot1(&entry, prf_secret, vault_aad)
                    .expect("Slot 1 DEK アンラップに成功。"),
            ));
            assert_eq!(unwrapped.as_bytes(), &DEK_SENTINEL);
            drop(unwrapped);
            entry
        });

        run_with_heap_leak_check(&[&DEK_SENTINEL, &kek1, prf_secret], 1, || {
            assert_eq!(
                unwrap_dek_slot1(&slot1_entry, &[0x99u8; 32], vault_aad).err(),
                Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
            );
            assert_eq!(
                unwrap_dek_slot1(&slot1_entry, prf_secret, wrong_aad).err(),
                Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
            );
        });

        // 3. Slot 2 (正準化付きリカバリーコード) の正常終了・エラー返却時メモリ衛生。
        let slot2_entry =
            run_with_heap_leak_check(&[&DEK_SENTINEL, &kek2, recovery_code_canonical], 4, || {
                let entry = wrap_dek_slot2_code(
                    &dek,
                    recovery_code_formatted,
                    &slot2_salt,
                    &slot2_nonce,
                    vault_aad,
                )
                .expect("Slot 2 DEK ラップに成功。");
                let unwrapped = core::hint::black_box(Box::new(
                    unwrap_dek_slot2_code(&entry, recovery_code_formatted, vault_aad)
                        .expect("Slot 2 DEK アンラップに成功。"),
                ));
                assert_eq!(unwrapped.as_bytes(), &DEK_SENTINEL);
                drop(unwrapped);
                entry
            });

        // 正準化途中の不正文字注入エラー・長さ不足エラー・MAC 不一致エラーでも中間バッファが残留しない。
        let partial_bad_code = b"abcd-efgh-ijkl-mnop-qrst-!xyz";
        let partial_prefix = b"ABCDEFGHIJKLMNOPQRST";
        let short_code = b"abcd-efgh-ijkl-mnop-qrst-uvw";
        let short_canonical = b"ABCDEFGHIJKLMNOPQRSTUVW";
        let wrong_code = b"ZZZZ-ZZZZ-ZZZZ-ZZZZ-ZZZZ-ZZZZ-ZZZZ";
        let wrong_canonical = b"ZZZZZZZZZZZZZZZZZZZZZZZZZZZZ";

        run_with_heap_leak_check(
            &[
                &DEK_SENTINEL,
                &kek2,
                recovery_code_canonical,
                partial_prefix,
                short_canonical,
                wrong_canonical,
            ],
            5,
            || {
                assert_eq!(
                    normalize_recovery_code(partial_bad_code).err(),
                    Some(VaultError::Crypto(CryptoError::InvalidParameter))
                );
                assert_eq!(
                    normalize_recovery_code(short_code).err(),
                    Some(VaultError::Crypto(CryptoError::InvalidKeySize))
                );
                assert_eq!(
                    unwrap_dek_slot2_code(&slot2_entry, wrong_code, vault_aad).err(),
                    Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
                );
                assert_eq!(
                    unwrap_dek_slot2_code(&slot2_entry, recovery_code_formatted, wrong_aad).err(),
                    Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
                );
            },
        );
    }

    #[test]
    fn test_vault_engine_unlock_lock_zeroize_drop_memory_hygiene() {
        let params = Argon2Params::fast_test();
        let dek = SecretBytes::new(DEK_SENTINEL);
        let password = b"FIDELOGIC_VAULT_PASSWORD_SECRET!";
        let slot0_salt: [u8; SLOT0_SALT_LEN] = *b"vault-slot0-salt";
        let slot0_nonce: [u8; SLOT0_NONCE_LEN] = *b"vault-slot0-nonce-24byte";

        let prf_secret = b"FIDELOGIC_VAULT_PRF_SECRET_32BYT";
        let slot1_salt: [u8; SLOT1_SALT_LEN] = *b"vault-slot1-hkdf-salt-32-bytes01";
        let slot1_nonce: [u8; SLOT1_NONCE_LEN] = *b"vault-slot1-nonce-24byte";

        let recovery_code_formatted = b"r3c0-v3ry-c0d3-f1d3-10g1-c202-6vau";
        let recovery_code_canonical = b"R3C0V3RYC0D3F1D310G1C2026VAU";
        let slot2_salt: [u8; SLOT2_SALT_LEN] = *b"vault-slot2-hkdf-salt-32-bytes02";
        let slot2_nonce: [u8; SLOT2_NONCE_LEN] = *b"vault-slot2-nonce-24byte";

        let engine_test_for_suite = |suite: CipherSuiteId, record_nonce: &[u8]| {
            let header = VaultHeader::new(1, suite.as_u8(), 7);
            let aad = header.associated_data();

            let slot0 = wrap_dek_slot0(&dek, password, &slot0_salt, &slot0_nonce, &params, &aad)
                .expect("Vault 用 Slot 0 生成に成功。");
            let slot1 = wrap_dek_slot1(&dek, prf_secret, &slot1_salt, &slot1_nonce, &aad)
                .expect("Vault 用 Slot 1 生成に成功。");
            let slot2 = wrap_dek_slot2_code(
                &dek,
                recovery_code_formatted,
                &slot2_salt,
                &slot2_nonce,
                &aad,
            )
            .expect("Vault 用 Slot 2 生成に成功。");

            // DEK で暗号化した Vault レコードペイロードを準備する。
            let plaintext = make_plaintext_64();
            let entry_cipher = VaultCipher::new_from_secret(suite, &dek);
            let mut entry_ct = plaintext;
            let entry_tag = entry_cipher
                .encrypt_in_place_detached(record_nonce, &aad, &mut entry_ct)
                .expect("Vault エントリ暗号化に成功。");
            drop(entry_cipher);

            let vault = Vault::new(
                header,
                vec![slot0, slot1, slot2],
                vec![TlvRecord::Entry(EntryPayload::new(
                    entry_ct.to_vec(),
                    entry_tag,
                ))],
            );

            let kek0 = *params
                .derive_key_32(password, &slot0_salt)
                .expect("Slot 0 KEK 事前計算に成功。")
                .as_bytes();
            let kek1 = *hkdf_sha256_derive_32(
                &slot1_salt,
                prf_secret,
                b"fidelogic-slot1-hkdf-sha256-kek-v1",
            )
            .expect("Slot 1 KEK 事前計算に成功。")
            .as_bytes();
            let kek2 = *hkdf_sha256_derive_32(
                &slot2_salt,
                recovery_code_canonical,
                b"fidelogic-slot2-recovery-hkdf-sha256-kek-v1",
            )
            .expect("Slot 2 KEK 事前計算に成功。")
            .as_bytes();

            let watched_patterns: [&[u8]; 7] = [
                &DEK_SENTINEL,
                &PLAINTEXT_SENTINEL,
                &kek0,
                &kek1,
                &kek2,
                password,
                recovery_code_canonical,
            ];

            // シナリオ A: 解錠 -> レコード暗号化・復号 -> lock() -> Box<VaultEngine> 破棄。
            run_with_heap_leak_check(&watched_patterns, 4, || {
                let mut engine = Box::new(
                    VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(params),
                );
                engine
                    .unlock_vault_with_password(&vault, password)
                    .expect("Slot 0 経由での Vault 解錠に成功。");
                assert_eq!(engine.state(), VaultState::Unlocked);

                let decrypted = engine
                    .with_dek(|unlocked_dek| {
                        let c = VaultCipher::new_from_secret(suite, unlocked_dek);
                        let new_ct = c.encrypt(record_nonce, &plaintext, &aad)?;
                        drop(new_ct);
                        let TlvRecord::Entry(ref entry) = vault.records[0] else {
                            unreachable!();
                        };
                        let mut combined = entry.ciphertext.clone();
                        combined.extend_from_slice(&entry.auth_tag);
                        c.decrypt(record_nonce, &combined, &aad)
                    })
                    .expect("DEK 取得に成功。")
                    .expect("Vault レコード復号に成功。");
                assert_eq!(decrypted.as_slice(), &plaintext);
                drop(decrypted);

                engine.lock().expect("lock() に成功。");
                assert_eq!(engine.state(), VaultState::Locked);
                assert!(engine.observe_dek().is_none());
                assert!(engine.is_safe_state());
                drop(engine);
            });

            // シナリオ B: 多重化解錠(unlock_vault_with_any + ダミー演算含む) -> zeroize_key() -> 破棄。
            run_with_heap_leak_check(&watched_patterns, 4, || {
                let mut engine = Box::new(
                    VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(params),
                );
                let creds = [
                    SlotCredential::prf(prf_secret),
                    SlotCredential::password(password),
                    SlotCredential::recovery_code(recovery_code_formatted),
                ];
                let matched = engine
                    .unlock_vault_with_any(&vault, &creds)
                    .expect("多重化解錠に成功。");
                assert_eq!(matched.as_slot_id(), SLOT_ID_PRF);

                engine.zeroize_key().expect("zeroize_key() に成功。");
                assert_eq!(engine.state(), VaultState::Zeroized);
                assert!(engine.observe_dek().is_none());
                assert!(engine.is_safe_state());
                drop(engine);
            });

            // シナリオ C: 解錠状態のまま lock() せず Box<VaultEngine> を Drop(RAII フェイルセーフ消去)。
            run_with_heap_leak_check(&watched_patterns, 4, || {
                let mut engine = Box::new(
                    VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(params),
                );
                engine
                    .unlock_vault_with_all_slots(
                        &vault,
                        &[SlotCredential::recovery_code(recovery_code_formatted)],
                    )
                    .expect("全スロット平滑化解錠に成功。");
                assert_eq!(engine.state(), VaultState::Unlocked);
                drop(engine);
            });

            // シナリオ D: 解錠エラー返却後(認証失敗・全資格情報失敗・complete_unlock 拒絶)。
            run_with_heap_leak_check(&watched_patterns, 4, || {
                let mut engine = Box::new(
                    VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(params),
                );
                assert_eq!(
                    engine.unlock_vault_with_password(&vault, b"wrong-vault-password"),
                    Err(VaultError::AuthenticationFailed)
                );
                assert_eq!(engine.state(), VaultState::Locked);
                assert!(engine.is_safe_state());

                let bad_creds = [
                    SlotCredential::password(b"wrong-vault-password"),
                    SlotCredential::prf(&[0xEEu8; 32]),
                    SlotCredential::recovery_code(b"WR0N-GC0D-E000-0000-0000-0000-0000"),
                ];
                assert_eq!(
                    engine.unlock_vault_with_any(&vault, &bad_creds),
                    Err(VaultError::AuthenticationFailed)
                );
                assert_eq!(engine.state(), VaultState::Locked);
                assert!(engine.is_safe_state());

                // 状態遷移・スロット契約違反エラー時でも complete_unlock に渡された DEK は即座に消去される。
                engine
                    .set_slot_status(SlotKind::Recovery, SlotStatus::Invalid)
                    .expect("set_slot_status に成功。");
                engine
                    .start_unlock(SlotKind::Argon2id)
                    .expect("start_unlock に成功。");
                assert_eq!(
                    engine.complete_unlock(SlotKind::Recovery, SecretBytes::new(DEK_SENTINEL)),
                    Err(VaultError::AuthenticationFailed)
                );
                assert!(engine.observe_dek().is_none());
                assert!(engine.is_safe_state());
                assert_eq!(
                    engine.complete_unlock(SlotKind::Prf, SecretBytes::new(DEK_SENTINEL)),
                    Ok(())
                );
                assert_eq!(
                    engine.complete_unlock(SlotKind::Argon2id, SecretBytes::new(DEK_SENTINEL)),
                    Err(VaultError::InvalidState)
                );
                drop(engine);
            });
        };

        engine_test_for_suite(
            CipherSuiteId::XChaCha20Poly1305,
            &[0x66u8; XCHACHA20_POLY1305_NONCE_LEN],
        );
        engine_test_for_suite(
            CipherSuiteId::Aes256GcmSiv,
            &[0x77u8; AES_256_GCM_SIV_NONCE_LEN],
        );
    }

    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 64,
            failure_persistence: None,
            ..ProptestConfig::default()
        })]

        #[test]
        fn prop_random_encrypt_decrypt_and_slot_unlock_memory_hygiene(
            mut raw_dek in any::<[u8; 32]>(),
            mut raw_pt in any::<[u8; 64]>(),
            mut raw_prf in any::<[u8; 32]>(),
            salt in any::<[u8; 32]>(),
            nonce in any::<[u8; 24]>(),
            use_aes in any::<bool>(),
            pt_len in 32usize..=64usize,
            tamper_idx in 0usize..16usize,
        ) {
            // ゼロ埋めメモリと区別するため先頭バイトを確実に非ゼロ化する。
            raw_dek[0] |= 0x81;
            raw_pt[0] |= 0x42;
            raw_prf[0] |= 0x24;

            let suite = if use_aes {
                CipherSuiteId::Aes256GcmSiv
            } else {
                CipherSuiteId::XChaCha20Poly1305
            };
            let cipher_nonce = &nonce[..suite.nonce_len()];
            let aad = b"proptest-memory-hygiene-aad";
            let pt_slice = &raw_pt[..pt_len];
            let pt_watch = &raw_pt[..32];

            // 1. ランダム平文・ランダム DEK での暗号化・復号(正常終了とタグ改ざんエラー)のメモリ衛生。
            let ct = run_with_heap_leak_check(&[&raw_dek, pt_watch], 1, || {
                let cipher = core::hint::black_box(Box::new(VaultCipher::new(suite, &raw_dek)));
                let encrypted = cipher
                    .encrypt(cipher_nonce, pt_slice, aad)
                    .expect("ランダム平文の暗号化に成功。");
                let decrypted = cipher
                    .decrypt(cipher_nonce, &encrypted, aad)
                    .expect("ランダム暗号文の復号に成功。");
                prop_assert_eq!(decrypted.as_slice(), pt_slice);
                drop(decrypted);
                drop(cipher);
                Ok(encrypted)
            })?;

            // インプレース復号の改ざんエラー時ゼロクリアと、alloc 復号失敗時の非残留を検証する。
            let mut tampered_ct = ct.clone();
            let tag_offset = pt_len + tamper_idx;
            tampered_ct[tag_offset] ^= 0xFF;

            let mut in_place_buf = [0u8; 64];
            in_place_buf[..pt_len].copy_from_slice(&ct[..pt_len]);
            let mut bad_tag = [0u8; TAG_LEN];
            bad_tag.copy_from_slice(&tampered_ct[pt_len..]);

            run_with_heap_leak_check(&[&raw_dek, pt_watch], 2, || {
                let cipher = core::hint::black_box(Box::new(VaultCipher::new(suite, &raw_dek)));
                prop_assert_eq!(
                    cipher.decrypt(cipher_nonce, &tampered_ct, aad).err(),
                    Some(CryptoError::AeadDecryptionFailed)
                );
                prop_assert_eq!(
                    cipher.decrypt_in_place_detached_tag(
                        cipher_nonce,
                        aad,
                        &mut in_place_buf[..pt_len],
                        &bad_tag,
                    ),
                    Err(CryptoError::AeadDecryptionFailed)
                );
                prop_assert!(in_place_buf[..pt_len].iter().all(|&b| b == 0));
                drop(cipher);
                Ok(())
            })?;

            // 2. ランダム DEK・ランダム PRF での Slot 1 ラップ/アンラップ(正常・失敗)および VaultEngine 衛生。
            let kek = *hkdf_sha256_derive_32(
                &salt,
                &raw_prf,
                b"fidelogic-slot1-hkdf-sha256-kek-v1",
            )
            .expect("プロパティーテスト用 KEK 計算に成功。")
            .as_bytes();
            let dek_secret = SecretBytes::new(raw_dek);
            let slot1 = wrap_dek_slot1(&dek_secret, &raw_prf, &salt, &nonce, aad)
                .expect("ランダム Slot 1 生成に成功。");

            let header = VaultHeader::new(1, suite.as_u8(), 1);
            let slot_aad = header.associated_data();
            let slot1_for_vault = wrap_dek_slot1(&dek_secret, &raw_prf, &salt, &nonce, &slot_aad)
                .expect("Vault ヘッダーバインド Slot 1 生成に成功。");
            let vault = Vault::new(header, vec![slot1_for_vault], Vec::new());

            run_with_heap_leak_check(&[&raw_dek, &kek, &raw_prf], 3, || {
                let unwrapped = core::hint::black_box(Box::new(
                    unwrap_dek_slot1(&slot1, &raw_prf, aad)
                        .expect("ランダム Slot 1 復号に成功。"),
                ));
                prop_assert_eq!(unwrapped.as_bytes(), &raw_dek);
                drop(unwrapped);

                let mut engine = Box::new(VaultEngine::from_slot_entries(&vault.slots));
                engine
                    .unlock_vault_with_prf(&vault, &raw_prf)
                    .expect("ランダム PRF 解錠に成功。");
                engine.lock().expect("lock() に成功。");
                drop(engine);

                let mut engine_fail = Box::new(VaultEngine::from_slot_entries(&vault.slots));
                let mut wrong_prf = raw_prf;
                wrong_prf[0] ^= 0xFF;
                prop_assert_eq!(
                    engine_fail.unlock_vault_with_prf(&vault, &wrong_prf),
                    Err(VaultError::AuthenticationFailed)
                );
                drop(engine_fail);
                Ok(())
            })?;
        }
    }
}
