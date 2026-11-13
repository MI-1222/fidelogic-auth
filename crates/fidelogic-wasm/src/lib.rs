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

/// Wasm C ABI 関数の処理結果を表すステータスコード。
///
/// 外部 C ABI 関数の戻り値(`u32`)に対応し、成否とエラーの種類を型安全に表す。
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmStatusCode {
    /// 処理が正常に完了。
    Success = 0,
    /// 引数ポインタが NULL、またはバッファが必要な最小の長さを満たさない。
    InvalidPointer = 1,
    /// 指定された暗号スイートID・鍵長・入力パラメータが不正。
    InvalidParameter = 2,
    /// 暗号演算・鍵導出・デシリアライズ処理に失敗。
    ExecutionFailed = 3,
}

impl WasmStatusCode {
    /// C ABI 戻り値向けの `u32` 値に変換する。
    #[inline]
    #[must_use]
    pub const fn as_u32(self) -> u32 {
        self as u32
    }
}

impl From<WasmStatusCode> for u32 {
    #[inline]
    fn from(code: WasmStatusCode) -> Self {
        code as u32
    }
}

/// 不正なスライスポインタまたは `isize::MAX` を超える長さを検証し、安全に不変スライスを取得する。
///
/// `len == 0` の場合はポインタが NULL であっても安全に空スライス `&[]` を返す。
/// `len > 0` の場合は `ptr` が非NULLかつ `len <= isize::MAX as usize` であることを検証する。
#[allow(dead_code)]
#[inline]
unsafe fn slice_from_raw_parts_checked<'a>(
    ptr: *const u8,
    len: usize,
) -> Result<&'a [u8], WasmStatusCode> {
    if len == 0 {
        Ok(&[])
    } else if ptr.is_null() || len > isize::MAX as usize {
        Err(WasmStatusCode::InvalidPointer)
    } else {
        // SAFETY: 呼び出し元が `ptr` の有効性とエイリアシング契約を保証し、`len <= isize::MAX` かつ非NULL。
        Ok(unsafe { core::slice::from_raw_parts(ptr, len) })
    }
}

/// 不正なスライスポインタまたは `isize::MAX` を超える長さを検証し、安全に可変スライスを取得する。
///
/// `len == 0` の場合はポインタが NULL であっても安全に空スライス `&mut []` を返す。
/// `len > 0` の場合は `ptr` が非NULLかつ `len <= isize::MAX as usize` であることを検証する。
#[allow(dead_code)]
#[inline]
unsafe fn slice_from_raw_parts_mut_checked<'a>(
    ptr: *mut u8,
    len: usize,
) -> Result<&'a mut [u8], WasmStatusCode> {
    if len == 0 {
        Ok(&mut [])
    } else if ptr.is_null() || len > isize::MAX as usize {
        Err(WasmStatusCode::InvalidPointer)
    } else {
        // SAFETY: 呼び出し元が `ptr` の有効性と排他性を保証し、`len <= isize::MAX` かつ非NULL。
        Ok(unsafe { core::slice::from_raw_parts_mut(ptr, len) })
    }
}

/// 2つのメモリ領域 `[a_ptr, a_ptr + a_len)` と `[b_ptr, b_ptr + b_len)` が重複しているかを検証する。
///
/// どちらかの長さが 0 の場合はアクセスが発生しないため重複なし(`false`)と判定する。
/// アドレス計算には [`usize::saturating_add`] を用い、オーバーフローによる未定義動作を抑止する。
#[inline]
fn ranges_overlap(a_ptr: *const u8, a_len: usize, b_ptr: *const u8, b_len: usize) -> bool {
    if a_len == 0 || b_len == 0 {
        return false;
    }
    let a_start = a_ptr as usize;
    let b_start = b_ptr as usize;
    let a_end = a_start.saturating_add(a_len);
    let b_end = b_start.saturating_add(b_len);
    a_start < b_end && b_start < a_end
}

/// 現在リンクされているコアエンジンのプロファイルステータスコードを取得する。
///
/// 外部C ABIからも直接呼び出し可能なインターフェース骨格。
/// プロファイルが有効な場合は `1`、未設定(`""` または `"none"`)の場合は `0` を返す。
#[unsafe(no_mangle)]
pub extern "C" fn fidelogic_wasm_status() -> u32 {
    let profile = active_profile();
    if profile.is_empty() || profile == "none" {
        0
    } else {
        1
    }
}

#[cfg(any(test, feature = "ci-inspection"))]
/// Dead Store Elimination (DSE) 抑止検査用の外部C ABIエクスポート関数。
///
/// 指定されたメモリ領域に対して揮発性ゼロ書き込みを実施する。
/// 内部で [`fidelogic_core::zeroize::volatile_zeroize`] を呼び出す。
///
/// # Safety
/// 呼び出し元は `ptr` が有効であり、少なくとも `len` バイトの連続した書き込み可能メモリを指していることを保証しなければならない。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_zeroize_test(ptr: *mut u8, len: usize) {
    if let Ok(slice) = unsafe { slice_from_raw_parts_mut_checked(ptr, len) }
        && !slice.is_empty()
    {
        fidelogic_core::zeroize::volatile_zeroize(slice);
    }
}

#[cfg(any(test, feature = "ci-inspection"))]
/// 定数時間暗号照合ブロック(32バイト認証タグ・トークン照合)の外部C ABIエクスポート関数。
///
/// 暗号照合ブロック内部にコンパイラ最適化による早期リターンや
/// 条件分岐命令(`br_if`, `if`, `br_table`)が注入されていないかを機械的静的検査で検証するための対象関数。
/// `a_ptr` または `b_ptr` が NULL の場合は分岐命令を発生させずに `0`(不一致)を返す。
///
/// # Safety
/// 呼び出し元は非NULLの `a_ptr` および `b_ptr` について、それぞれ少なくとも32バイトの連続した
/// 読み取り可能メモリ領域を指していることを保証しなければならない。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_constant_time_eq_32(
    a_ptr: *const u8,
    b_ptr: *const u8,
) -> u32 {
    static ZERO_BLOCK: [u8; 32] = [0u8; 32];
    let a_non_null = !a_ptr.is_null();
    let b_non_null = !b_ptr.is_null();
    let safe_a_ptr = core::hint::select_unpredictable(a_non_null, a_ptr, ZERO_BLOCK.as_ptr());
    let safe_b_ptr = core::hint::select_unpredictable(b_non_null, b_ptr, ZERO_BLOCK.as_ptr());
    let a = unsafe { &*(safe_a_ptr as *const [u8; 32]) };
    let b = unsafe { &*(safe_b_ptr as *const [u8; 32]) };
    let eq = fidelogic_core::ct_eq_32(a, b).unwrap_u8() as u32;
    let valid = (a_non_null & b_non_null) as u32;
    eq & valid
}

/// TLV Vault ヘッダーのデシリアライズを行う外部C ABIエクスポート関数。
///
/// # Safety
/// 呼び出し元は `header_bytes_ptr` が有効であり、少なくとも `len` バイトの
/// 読み取り可能メモリ領域を指していることを保証しなければならない。
/// また、`out_suite_id` および `out_epoch_id` は非NULLであり、それぞれ 1 バイトおよび
/// 8 バイトの書き込み可能メモリ領域を指している必要がある(`out_epoch_id` は非アライン可)。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_header_parse(
    header_bytes_ptr: *const u8,
    len: usize,
    out_suite_id: *mut u8,
    out_epoch_id: *mut u64,
) -> u32 {
    if header_bytes_ptr.is_null()
        || out_suite_id.is_null()
        || out_epoch_id.is_null()
        || len < fidelogic_core::tlv::VAULT_HEADER_LEN
        || len > isize::MAX as usize
    {
        return WasmStatusCode::InvalidPointer.as_u32();
    }
    // SAFETY: 事前検証により `header_bytes_ptr` は非NULLであり、少なくとも VAULT_HEADER_LEN バイトの
    // 有効なメモリ領域を指している。先頭のヘッダー部分のみをスライス化することで安全性を担保する。
    let slice = unsafe {
        core::slice::from_raw_parts(header_bytes_ptr, fidelogic_core::tlv::VAULT_HEADER_LEN)
    };
    match fidelogic_core::tlv::deserialize_header(slice) {
        Ok((header, _)) => {
            unsafe {
                *out_suite_id = header.suite_id;
                // JS/Wasm 側のパック済みバッファ等からの非アラインポインタ渡しでも未定義動作にならないよう書き込む。
                core::ptr::write_unaligned(out_epoch_id, header.epoch_id);
            }
            WasmStatusCode::Success.as_u32()
        }
        Err(_) => WasmStatusCode::InvalidParameter.as_u32(),
    }
}

#[cfg(any(feature = "profile-lite", feature = "profile-vault"))]
/// RFC 7748 X25519 Diffie-Hellman 鍵共有演算の外部C ABIエクスポート関数。
///
/// # Safety
/// 呼び出し元は `secret_key_ptr`, `public_key_ptr`, `out_shared_ptr` が有効であり、
/// それぞれ32バイトのメモリ領域を指していることを保証しなければならない。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_x25519_dh(
    secret_key_ptr: *const u8,
    public_key_ptr: *const u8,
    out_shared_ptr: *mut u8,
) -> u32 {
    if secret_key_ptr.is_null() || public_key_ptr.is_null() || out_shared_ptr.is_null() {
        return WasmStatusCode::InvalidPointer.as_u32();
    }
    if ranges_overlap(secret_key_ptr, 32, out_shared_ptr, 32)
        || ranges_overlap(public_key_ptr, 32, out_shared_ptr, 32)
    {
        return WasmStatusCode::InvalidPointer.as_u32();
    }
    let key_arr = unsafe { &*(secret_key_ptr as *const [u8; 32]) };
    let secret = fidelogic_core::SecretBytes::new(*key_arr);
    let public_arr = unsafe { &*(public_key_ptr as *const [u8; 32]) };
    let public = fidelogic_core::X25519PublicKey::new(*public_arr);
    match fidelogic_core::x25519_diffie_hellman(&secret, &public) {
        Ok(shared) => {
            let out_slice = unsafe { core::slice::from_raw_parts_mut(out_shared_ptr, 32) };
            out_slice.copy_from_slice(shared.as_bytes());
            WasmStatusCode::Success.as_u32()
        }
        Err(_) => {
            let out_slice = unsafe { core::slice::from_raw_parts_mut(out_shared_ptr, 32) };
            fidelogic_core::zeroize::volatile_zeroize(out_slice);
            WasmStatusCode::InvalidParameter.as_u32()
        }
    }
}

#[cfg(feature = "profile-vault")]
/// Argon2id 鍵導出の外部C ABIエクスポート関数。
///
/// Wasm環境向け本番パラメータ([`fidelogic_core::Argon2Params::for_wasm`]: 19 MiB, t=2, p=1)を適用し、
/// 指定された出力長 `out_len` で鍵を導出する。
///
/// # Safety
/// 呼び出し元は各ポインタが有効であり、指定された長さのメモリ領域を指していることを保証しなければならない。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_kdf_derive_key(
    password_ptr: *const u8,
    password_len: usize,
    salt_ptr: *const u8,
    salt_len: usize,
    out_ptr: *mut u8,
    out_len: usize,
) -> u32 {
    if ranges_overlap(password_ptr, password_len, out_ptr, out_len)
        || ranges_overlap(salt_ptr, salt_len, out_ptr, out_len)
    {
        return WasmStatusCode::InvalidPointer.as_u32();
    }

    let password = match unsafe { slice_from_raw_parts_checked(password_ptr, password_len) } {
        Ok(s) => s,
        Err(code) => return code.as_u32(),
    };
    let salt = match unsafe { slice_from_raw_parts_checked(salt_ptr, salt_len) } {
        Ok(s) => s,
        Err(code) => return code.as_u32(),
    };
    let out = match unsafe { slice_from_raw_parts_mut_checked(out_ptr, out_len) } {
        Ok(s) => s,
        Err(code) => return code.as_u32(),
    };

    let params = match fidelogic_core::Argon2Params::for_wasm()
        .with_output_len(out_len)
        .validated()
    {
        Ok(p) => p,
        Err(_) => {
            if !out.is_empty() {
                fidelogic_core::zeroize::volatile_zeroize(out);
            }
            return WasmStatusCode::InvalidParameter.as_u32();
        }
    };

    match params.derive_key(password, salt, out) {
        Ok(()) => WasmStatusCode::Success.as_u32(),
        Err(_) => {
            if !out.is_empty() {
                fidelogic_core::zeroize::volatile_zeroize(out);
            }
            WasmStatusCode::ExecutionFailed.as_u32()
        }
    }
}

/// Vault暗号化・復号C ABI関数の共通検証結果を表す構造体。
#[cfg(feature = "profile-vault")]
struct VaultOpParams<'a> {
    cipher: fidelogic_core::VaultCipher,
    nonce: &'a [u8],
    aad: &'a [u8],
    data: &'a mut [u8],
}

/// Vault暗号化・復号C ABI関数向けの共通引数検証およびスライス構築ヘルパー。
///
/// # Safety
/// 非NULLの各ポインタは指定された長さの有効なメモリ領域を指し、
/// 返却されるライフタイム `'a` の間は他の参照とエイリアシング規則に違反しないこと。
#[cfg(feature = "profile-vault")]
#[allow(clippy::too_many_arguments)]
unsafe fn parse_vault_params<'a>(
    suite_id: u8,
    key_ptr: *const u8,
    nonce_ptr: *const u8,
    nonce_len: usize,
    aad_ptr: *const u8,
    aad_len: usize,
    data_ptr: *mut u8,
    data_len: usize,
) -> Result<VaultOpParams<'a>, WasmStatusCode> {
    if key_ptr.is_null() || nonce_ptr.is_null() {
        return Err(WasmStatusCode::InvalidPointer);
    }
    if ranges_overlap(key_ptr, fidelogic_core::KEY_LEN, data_ptr, data_len)
        || ranges_overlap(nonce_ptr, nonce_len, data_ptr, data_len)
        || ranges_overlap(aad_ptr, aad_len, data_ptr, data_len)
    {
        return Err(WasmStatusCode::InvalidPointer);
    }
    let suite = fidelogic_core::CipherSuiteId::from_u8(suite_id)
        .map_err(|_| WasmStatusCode::InvalidParameter)?;
    let key = unsafe { &*(key_ptr as *const [u8; fidelogic_core::KEY_LEN]) };
    let cipher = fidelogic_core::VaultCipher::new(suite, key);

    let nonce = unsafe { slice_from_raw_parts_checked(nonce_ptr, nonce_len)? };
    let aad = unsafe { slice_from_raw_parts_checked(aad_ptr, aad_len)? };
    let data = unsafe { slice_from_raw_parts_mut_checked(data_ptr, data_len)? };

    Ok(VaultOpParams {
        cipher,
        nonce,
        aad,
        data,
    })
}

#[cfg(feature = "profile-vault")]
/// Vault インプレース分離暗号化の外部C ABIエクスポート関数。
///
/// # Safety
/// 各ポインタは指定された長さの有効なメモリ領域を指していること。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_vault_encrypt(
    suite_id: u8,
    key_ptr: *const u8,
    nonce_ptr: *const u8,
    nonce_len: usize,
    aad_ptr: *const u8,
    aad_len: usize,
    data_ptr: *mut u8,
    data_len: usize,
    tag_out_ptr: *mut u8,
) -> u32 {
    if tag_out_ptr.is_null() {
        return WasmStatusCode::InvalidPointer.as_u32();
    }
    if ranges_overlap(
        key_ptr,
        fidelogic_core::KEY_LEN,
        tag_out_ptr,
        fidelogic_core::TAG_LEN,
    ) || ranges_overlap(nonce_ptr, nonce_len, tag_out_ptr, fidelogic_core::TAG_LEN)
        || ranges_overlap(aad_ptr, aad_len, tag_out_ptr, fidelogic_core::TAG_LEN)
        || ranges_overlap(data_ptr, data_len, tag_out_ptr, fidelogic_core::TAG_LEN)
    {
        return WasmStatusCode::InvalidPointer.as_u32();
    }
    let params = match unsafe {
        parse_vault_params(
            suite_id, key_ptr, nonce_ptr, nonce_len, aad_ptr, aad_len, data_ptr, data_len,
        )
    } {
        Ok(p) => p,
        Err(code) => return code.as_u32(),
    };

    match params
        .cipher
        .encrypt_in_place_detached(params.nonce, params.aad, params.data)
    {
        Ok(tag) => {
            let tag_out =
                unsafe { core::slice::from_raw_parts_mut(tag_out_ptr, fidelogic_core::TAG_LEN) };
            tag_out.copy_from_slice(&tag);
            WasmStatusCode::Success.as_u32()
        }
        Err(_) => WasmStatusCode::ExecutionFailed.as_u32(),
    }
}

#[cfg(feature = "profile-vault")]
/// Vault インプレース分離復号の外部C ABIエクスポート関数。
///
/// # Safety
/// 各ポインタは指定された長さの有効なメモリ領域を指していること。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_vault_decrypt(
    suite_id: u8,
    key_ptr: *const u8,
    nonce_ptr: *const u8,
    nonce_len: usize,
    aad_ptr: *const u8,
    aad_len: usize,
    data_ptr: *mut u8,
    data_len: usize,
    tag_ptr: *const u8,
) -> u32 {
    if tag_ptr.is_null() {
        return WasmStatusCode::InvalidPointer.as_u32();
    }
    if ranges_overlap(tag_ptr, fidelogic_core::TAG_LEN, data_ptr, data_len) {
        return WasmStatusCode::InvalidPointer.as_u32();
    }
    let params = match unsafe {
        parse_vault_params(
            suite_id, key_ptr, nonce_ptr, nonce_len, aad_ptr, aad_len, data_ptr, data_len,
        )
    } {
        Ok(p) => p,
        Err(code) => return code.as_u32(),
    };
    let tag = unsafe { core::slice::from_raw_parts(tag_ptr, fidelogic_core::TAG_LEN) };

    match params
        .cipher
        .decrypt_in_place_detached(params.nonce, params.aad, params.data, tag)
    {
        Ok(()) => WasmStatusCode::Success.as_u32(),
        Err(_) => WasmStatusCode::ExecutionFailed.as_u32(),
    }
}

#[cfg(feature = "profile-vault")]
/// Vault 全体のTLVデシリアライズ検証の外部C ABIエクスポート関数。
///
/// # Safety
/// 各ポインタは指定された長さの有効なメモリ領域を指していること。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_vault_deserialize(bytes_ptr: *const u8, len: usize) -> u32 {
    let bytes = match unsafe { slice_from_raw_parts_checked(bytes_ptr, len) } {
        Ok(b) if !b.is_empty() => b,
        _ => return WasmStatusCode::InvalidPointer.as_u32(),
    };
    match fidelogic_core::tlv::deserialize(bytes) {
        Ok((_vault, _)) => WasmStatusCode::Success.as_u32(),
        Err(_) => WasmStatusCode::ExecutionFailed.as_u32(),
    }
}

#[cfg(all(feature = "profile-vault", any(test, feature = "ci-inspection")))]
/// サイズゲート計測用アンカー: LTOによる `tlv::serialize` のデッドコード除去を抑止する内部検証用スタブ。
///
/// 本番API([`fidelogic_wasm_vault_deserialize`])から再シリアライズ副作用を分離するために独立させており、
/// 通常運用からの呼び出しは想定しない。
///
/// # Safety
/// 各ポインタは指定された長さの有効なメモリ領域を指していること。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_size_anchor(bytes_ptr: *const u8, len: usize) -> u32 {
    let bytes = match unsafe { slice_from_raw_parts_checked(bytes_ptr, len) } {
        Ok(b) if !b.is_empty() => b,
        _ => return WasmStatusCode::InvalidPointer.as_u32(),
    };
    match fidelogic_core::tlv::deserialize(bytes) {
        Ok((vault, _)) => match fidelogic_core::tlv::serialize(&vault) {
            Ok(_) => WasmStatusCode::Success.as_u32(),
            Err(_) => WasmStatusCode::InvalidParameter.as_u32(),
        },
        Err(_) => WasmStatusCode::ExecutionFailed.as_u32(),
    }
}

#[cfg(all(feature = "profile-vault", any(test, feature = "ci-inspection")))]
/// CI 静的解析用エクスポート: ダミー暗号演算 (Argon2id, HKDF-SHA256, XChaCha20-Poly1305 AEAD) の DCE 抑止検証用スタブ。
///
/// # Safety
/// 各ポインタは指定された長さの有効なメモリ領域を指していること (NULL または長さ 0 の場合は空 AAD として扱う)。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_dummy_slot_eval_test(
    aad_ptr: *const u8,
    aad_len: usize,
) -> u32 {
    let aad = match unsafe { slice_from_raw_parts_checked(aad_ptr, aad_len) } {
        Ok(s) => s,
        Err(_) => &[],
    };
    let summary = fidelogic_core::slots::run_dummy_slot_eval_for_inspection(aad);
    let total_ops = summary.dummy_argon2id_ops + summary.dummy_hkdf_ops + summary.dummy_aead_ops;
    core::hint::black_box(total_ops as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_status_code_repr() {
        assert_eq!(WasmStatusCode::Success.as_u32(), 0);
        assert_eq!(u32::from(WasmStatusCode::InvalidPointer), 1);
        assert_eq!(WasmStatusCode::InvalidParameter.as_u32(), 2);
        assert_eq!(u32::from(WasmStatusCode::ExecutionFailed), 3);
    }

    #[test]
    fn test_wasm_status() {
        #[cfg(any(feature = "profile-lite", feature = "profile-vault"))]
        assert_eq!(fidelogic_wasm_status(), 1);
        #[cfg(all(not(feature = "profile-lite"), not(feature = "profile-vault")))]
        assert_eq!(fidelogic_wasm_status(), 0);
    }

    #[test]
    fn test_constant_time_eq_32() {
        let tag1 = [0x42u8; 32];
        let tag2 = [0x42u8; 32];
        let mut tag3 = [0x42u8; 32];
        tag3[31] = 0x43;
        let zero_tag = [0u8; 32];

        unsafe {
            assert_eq!(
                fidelogic_wasm_constant_time_eq_32(tag1.as_ptr(), tag2.as_ptr()),
                1
            );
            assert_eq!(
                fidelogic_wasm_constant_time_eq_32(tag1.as_ptr(), tag3.as_ptr()),
                0
            );
            assert_eq!(
                fidelogic_wasm_constant_time_eq_32(core::ptr::null(), tag1.as_ptr()),
                0,
                "a_ptrがNULLの場合は0を返却。"
            );
            assert_eq!(
                fidelogic_wasm_constant_time_eq_32(tag1.as_ptr(), core::ptr::null()),
                0,
                "b_ptrがNULLの場合は0を返却。"
            );
            assert_eq!(
                fidelogic_wasm_constant_time_eq_32(core::ptr::null(), core::ptr::null()),
                0,
                "両ポインタがNULLの場合も0を返却。"
            );
            assert_eq!(
                fidelogic_wasm_constant_time_eq_32(zero_tag.as_ptr(), core::ptr::null()),
                0,
                "ゼロ配列とNULLポインタの比較でも誤一致せず0を返却。"
            );
        }
    }

    #[test]
    fn test_header_parse() {
        let valid_header = [b'F', b'V', b'A', b'U', 1, 1, 0, 0, 0, 0, 0, 0, 0, 42];
        let mut suite_id = 0u8;
        let mut epoch_id = 0u64;

        unsafe {
            let res = fidelogic_wasm_header_parse(
                valid_header.as_ptr(),
                valid_header.len(),
                &mut suite_id,
                &mut epoch_id,
            );
            assert_eq!(res, 0, "ヘッダーパースに成功。");
            assert_eq!(suite_id, 1, "暗号スイートIDの取得に成功。");
            assert_eq!(epoch_id, 42, "世代カウンターの取得に成功。");

            // 長さ不足によるエラーの検証
            let invalid_res =
                fidelogic_wasm_header_parse(valid_header.as_ptr(), 5, &mut suite_id, &mut epoch_id);
            assert_eq!(invalid_res, 1, "長さ不足時の検証エラーに成功。");

            // isize::MAX 超過によるエラーの検証
            let overflow_res = fidelogic_wasm_header_parse(
                valid_header.as_ptr(),
                usize::MAX,
                &mut suite_id,
                &mut epoch_id,
            );
            assert_eq!(overflow_res, 1, "isize::MAX超過時の検証エラーに成功。");

            // VAULT_HEADER_LEN を超えるバッファが渡された場合でも先頭14バイトのみで安全にパースされる検証
            let extended_buf = [
                b'F', b'V', b'A', b'U', 1, 1, 0, 0, 0, 0, 0, 0, 0, 42, 0xFF, 0xFF,
            ];
            let extended_res = fidelogic_wasm_header_parse(
                extended_buf.as_ptr(),
                extended_buf.len(),
                &mut suite_id,
                &mut epoch_id,
            );
            assert_eq!(
                extended_res, 0,
                "先頭14バイトのみを参照したヘッダーパースに成功。"
            );
            assert_eq!(epoch_id, 42, "世代カウンターの取得に成功。");

            // NULLポインタ引数に対するエラーの検証
            let null_header_res = fidelogic_wasm_header_parse(
                core::ptr::null(),
                valid_header.len(),
                &mut suite_id,
                &mut epoch_id,
            );
            assert_eq!(
                null_header_res, 1,
                "ヘッダーポインタNULL時にエラーコード1を返却。"
            );

            let null_suite_res = fidelogic_wasm_header_parse(
                valid_header.as_ptr(),
                valid_header.len(),
                core::ptr::null_mut(),
                &mut epoch_id,
            );
            assert_eq!(
                null_suite_res, 1,
                "suite_id出力ポインタNULL時にエラーコード1を返却。"
            );

            let null_epoch_res = fidelogic_wasm_header_parse(
                valid_header.as_ptr(),
                valid_header.len(),
                &mut suite_id,
                core::ptr::null_mut(),
            );
            assert_eq!(
                null_epoch_res, 1,
                "epoch_id出力ポインタNULL時にエラーコード1を返却。"
            );

            // 非アラインポインタへの epoch_id 書き込みが安全に動作することを検証する。
            #[repr(align(8))]
            struct AlignedBuf([u8; 16]);
            let mut unaligned_buf = AlignedBuf([0u8; 16]);
            let unaligned_suite_ptr = unaligned_buf.0.as_mut_ptr();
            let unaligned_epoch_ptr = unaligned_buf.0.as_mut_ptr().add(1) as *mut u64;
            let unaligned_res = fidelogic_wasm_header_parse(
                valid_header.as_ptr(),
                valid_header.len(),
                unaligned_suite_ptr,
                unaligned_epoch_ptr,
            );
            assert_eq!(unaligned_res, 0, "非アライン出力ポインタでのパースに成功。");
            assert_eq!(
                unaligned_buf.0[0], 1,
                "先頭1バイトの暗号スイートID書き込みに成功。"
            );
            assert_eq!(
                core::ptr::read_unaligned(unaligned_epoch_ptr),
                42,
                "非アラインアドレスへの世代カウンター書き込みに成功。"
            );
        }
    }

    #[cfg(any(feature = "profile-lite", feature = "profile-vault"))]
    #[test]
    fn test_x25519_dh() {
        let priv_a = [0x01u8; 32];
        let pub_b =
            fidelogic_core::x25519_basepoint_mul(&fidelogic_core::SecretBytes::new([0x02u8; 32]));
        let mut shared = [0u8; 32];

        unsafe {
            let res = fidelogic_wasm_x25519_dh(
                priv_a.as_ptr(),
                pub_b.as_bytes().as_ptr(),
                shared.as_mut_ptr(),
            );
            assert_eq!(res, 0, "X25519 DH鍵共有に成功。");
            assert_ne!(shared, [0u8; 32], "非ゼロの共有秘密の導出に成功。");

            // 低位数点(全ゼロ公開鍵)による失敗時は、出力バッファの既存データがゼロ消去されることを検証する。
            let low_order_pub = [0u8; 32];
            shared.fill(0xAA);
            let fail_res = fidelogic_wasm_x25519_dh(
                priv_a.as_ptr(),
                low_order_pub.as_ptr(),
                shared.as_mut_ptr(),
            );
            assert_eq!(fail_res, 2, "低位数点検出時にエラーコード2を返却。");
            assert_eq!(
                shared, [0u8; 32],
                "X25519 DH失敗時に出力バッファがゼロ消去されたことを確認。"
            );
        }
    }

    #[cfg(feature = "profile-vault")]
    #[test]
    fn test_kdf_derive_key() {
        let password = b"master-password";
        let salt = [0x5au8; 16];
        let mut derived_key = [0u8; 32];
        let mut expected_wasm_key = [0u8; 32];
        let mut fast_test_key = [0u8; 32];

        fidelogic_core::Argon2Params::for_wasm()
            .derive_key(password, &salt, &mut expected_wasm_key)
            .expect("本番Wasmパラメータでの期待値導出に成功。");
        fidelogic_core::Argon2Params::fast_test()
            .derive_key(password, &salt, &mut fast_test_key)
            .expect("テスト用パラメータでの比較値導出に成功。");

        unsafe {
            let res = fidelogic_wasm_kdf_derive_key(
                password.as_ptr(),
                password.len(),
                salt.as_ptr(),
                salt.len(),
                derived_key.as_mut_ptr(),
                derived_key.len(),
            );
            assert_eq!(res, 0, "Argon2id鍵導出に成功。");
            assert_ne!(derived_key, [0u8; 32], "非ゼロ鍵の導出に成功。");
            assert_eq!(
                derived_key, expected_wasm_key,
                "Wasm本番用パラメータ(Argon2Params::for_wasm)の出力と一致。"
            );
            assert_ne!(
                derived_key, fast_test_key,
                "テスト用極小パラメータ(FAST_TEST_*)ではないことを確認。"
            );

            // 不正な出力長(out_len = 0)に対するパラメータ検証エラー(戻り値2)を確認。
            let invalid_res = fidelogic_wasm_kdf_derive_key(
                password.as_ptr(),
                password.len(),
                salt.as_ptr(),
                salt.len(),
                derived_key.as_mut_ptr(),
                0,
            );
            assert_eq!(invalid_res, 2, "不正な出力長に対してエラーコード2を返却。");

            // 空パスワード(password_ptr = NULL, password_len = 0)の許容と鍵導出成功を検証。
            let mut empty_pw_key = [0u8; 32];
            let empty_pw_res = fidelogic_wasm_kdf_derive_key(
                core::ptr::null(),
                0,
                salt.as_ptr(),
                salt.len(),
                empty_pw_key.as_mut_ptr(),
                empty_pw_key.len(),
            );
            assert_eq!(empty_pw_res, 0, "空パスワード(NULL, 0)での鍵導出に成功。");
            assert_ne!(
                empty_pw_key, [0u8; 32],
                "空パスワードからの非ゼロ鍵導出に成功。"
            );

            // isize::MAX 超過ポインタ・長さ引数のエラーコード1返却を検証。
            let overflow_pw_res = fidelogic_wasm_kdf_derive_key(
                password.as_ptr(),
                usize::MAX,
                salt.as_ptr(),
                salt.len(),
                derived_key.as_mut_ptr(),
                derived_key.len(),
            );
            assert_eq!(
                overflow_pw_res, 1,
                "password_len が isize::MAX 超過時にエラーコード1を返却。"
            );

            let overflow_salt_res = fidelogic_wasm_kdf_derive_key(
                password.as_ptr(),
                password.len(),
                salt.as_ptr(),
                usize::MAX,
                derived_key.as_mut_ptr(),
                derived_key.len(),
            );
            assert_eq!(
                overflow_salt_res, 1,
                "salt_len が isize::MAX 超過時にエラーコード1を返却。"
            );

            let overflow_out_res = fidelogic_wasm_kdf_derive_key(
                password.as_ptr(),
                password.len(),
                salt.as_ptr(),
                salt.len(),
                derived_key.as_mut_ptr(),
                usize::MAX,
            );
            assert_eq!(
                overflow_out_res, 1,
                "out_len が isize::MAX 超過時にエラーコード1を返却。"
            );

            // 不正な出力長(out_len = 3: RFC 9106最小出力長4バイト未満)での事前検証失敗時に、
            // 出力バッファの既存データがゼロ消去されることを検証。
            let mut dirty_buf = [0xBBu8; 3];
            let invalid_len_res = fidelogic_wasm_kdf_derive_key(
                password.as_ptr(),
                password.len(),
                salt.as_ptr(),
                salt.len(),
                dirty_buf.as_mut_ptr(),
                dirty_buf.len(),
            );
            assert_eq!(
                invalid_len_res, 2,
                "不正な出力長に対してエラーコード2を返却。"
            );
            assert_eq!(
                dirty_buf, [0u8; 3],
                "KDF事前検証失敗時に出力バッファがゼロ消去されたことを確認。"
            );
        }
    }

    #[cfg(feature = "profile-vault")]
    #[test]
    fn test_vault_encrypt_decrypt() {
        let key = [0x42u8; 32];
        let nonce = [0x24u8; 24]; // XChaCha20Poly1305 ノンス
        let aad = b"authenticated-aad";
        let original_data = b"secret-payload-data";
        let mut buffer = original_data.to_vec();
        let mut tag = [0u8; 16];

        unsafe {
            // 暗号化
            let enc_res = fidelogic_wasm_vault_encrypt(
                1, // XChaCha20Poly1305
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                buffer.as_mut_ptr(),
                buffer.len(),
                tag.as_mut_ptr(),
            );
            assert_eq!(enc_res, 0, "Vault暗号化に成功。");
            assert_ne!(
                buffer.as_slice(),
                original_data,
                "平文が暗号文に上書きされたことを確認。"
            );

            // 復号
            let dec_res = fidelogic_wasm_vault_decrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                buffer.as_mut_ptr(),
                buffer.len(),
                tag.as_ptr(),
            );
            assert_eq!(dec_res, 0, "Vault復号に成功。");
            assert_eq!(buffer.as_slice(), original_data, "平文の復元に成功。");

            // aad_len > 0 かつ aad_ptr == NULL はサイレント脱落させず引数エラー(1)で拒絶する。
            let mut untouched_buf = original_data.to_vec();
            let mut untouched_tag = [0u8; 16];
            let null_aad_enc_res = fidelogic_wasm_vault_encrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                core::ptr::null(),
                aad.len(),
                untouched_buf.as_mut_ptr(),
                untouched_buf.len(),
                untouched_tag.as_mut_ptr(),
            );
            assert_eq!(
                null_aad_enc_res, 1,
                "aad_len > 0 かつ aad_ptr == NULL の暗号化は引数エラー1を返却。"
            );
            assert_eq!(
                untouched_buf.as_slice(),
                original_data,
                "暗号化エラー時はデータバッファを変更しないことを確認。"
            );
            assert_eq!(
                untouched_tag, [0u8; 16],
                "暗号化エラー時は出力タグバッファを変更しないことを確認。"
            );

            // isize::MAX 超過時の引数エラー検証 (nonce_len, aad_len, data_len)
            let overflow_nonce_res = fidelogic_wasm_vault_encrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                usize::MAX,
                aad.as_ptr(),
                aad.len(),
                untouched_buf.as_mut_ptr(),
                untouched_buf.len(),
                untouched_tag.as_mut_ptr(),
            );
            assert_eq!(
                overflow_nonce_res, 1,
                "nonce_len が isize::MAX 超過時にエラーコード1を返却。"
            );

            let overflow_aad_res = fidelogic_wasm_vault_encrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                usize::MAX,
                untouched_buf.as_mut_ptr(),
                untouched_buf.len(),
                untouched_tag.as_mut_ptr(),
            );
            assert_eq!(
                overflow_aad_res, 1,
                "aad_len が isize::MAX 超過時にエラーコード1を返却。"
            );

            let overflow_data_res = fidelogic_wasm_vault_encrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                untouched_buf.as_mut_ptr(),
                usize::MAX,
                untouched_tag.as_mut_ptr(),
            );
            assert_eq!(
                overflow_data_res, 1,
                "data_len が isize::MAX 超過時にエラーコード1を返却。"
            );

            let null_aad_dec_res = fidelogic_wasm_vault_decrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                core::ptr::null(),
                aad.len(),
                untouched_buf.as_mut_ptr(),
                untouched_buf.len(),
                tag.as_ptr(),
            );
            assert_eq!(
                null_aad_dec_res, 1,
                "aad_len > 0 かつ aad_ptr == NULL の復号は引数エラー1を返却。"
            );
            assert_eq!(
                untouched_buf.as_slice(),
                original_data,
                "復号の引数エラー時はデータバッファを変更しないことを確認。"
            );

            // aad_len == 0 かつ aad_ptr == NULL は空AADとして正常に往復できることを確認する。
            let mut empty_aad_buf = original_data.to_vec();
            let mut empty_aad_tag = [0u8; 16];
            let empty_aad_enc_res = fidelogic_wasm_vault_encrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                core::ptr::null(),
                0,
                empty_aad_buf.as_mut_ptr(),
                empty_aad_buf.len(),
                empty_aad_tag.as_mut_ptr(),
            );
            assert_eq!(empty_aad_enc_res, 0, "空AAD(NULL, 0)での暗号化に成功。");
            let empty_aad_dec_res = fidelogic_wasm_vault_decrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                core::ptr::null(),
                0,
                empty_aad_buf.as_mut_ptr(),
                empty_aad_buf.len(),
                empty_aad_tag.as_ptr(),
            );
            assert_eq!(empty_aad_dec_res, 0, "空AAD(NULL, 0)での復号に成功。");
            assert_eq!(
                empty_aad_buf.as_slice(),
                original_data,
                "空AAD往復後の平文復元に成功。"
            );
        }
    }

    #[cfg(feature = "profile-vault")]
    #[test]
    fn test_vault_deserialize() {
        let header = [
            b'F', b'V', b'A', b'U', 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
        ];

        unsafe {
            let res = fidelogic_wasm_vault_deserialize(header.as_ptr(), header.len());
            assert_eq!(res, 0, "Vaultデシリアライズに成功。");

            let null_res = fidelogic_wasm_vault_deserialize(core::ptr::null(), header.len());
            assert_eq!(null_res, 1, "NULLポインタ指定時に引数エラー1を返却。");

            let empty_res = fidelogic_wasm_vault_deserialize(header.as_ptr(), 0);
            assert_eq!(empty_res, 1, "長さ0指定時に引数エラー1を返却。");

            let overflow_res = fidelogic_wasm_vault_deserialize(header.as_ptr(), usize::MAX);
            assert_eq!(overflow_res, 1, "isize::MAX超過時に引数エラー1を返却。");

            let invalid_res = fidelogic_wasm_vault_deserialize(header.as_ptr(), 4);
            assert_eq!(invalid_res, 3, "不正Vaultバイト列に対してエラー3を返却。");
        }
    }

    #[cfg(feature = "profile-vault")]
    #[test]
    fn test_size_anchor() {
        let header = [
            b'F', b'V', b'A', b'U', 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
        ];

        unsafe {
            let res = fidelogic_wasm_size_anchor(header.as_ptr(), header.len());
            assert_eq!(res, 0, "サイズ計測アンカーの往復処理に成功。");

            let overflow_res = fidelogic_wasm_size_anchor(header.as_ptr(), usize::MAX);
            assert_eq!(
                overflow_res, 1,
                "isize::MAX超過時にサイズアンカーでエラーコード1を返却。"
            );
        }
    }

    #[cfg(feature = "profile-vault")]
    #[test]
    fn test_dummy_slot_eval_test_export() {
        let aad = b"wasm_vault_aad_for_test";
        unsafe {
            let res = fidelogic_wasm_dummy_slot_eval_test(aad.as_ptr(), aad.len());
            assert_eq!(
                res, 6,
                "ダミー暗号演算パイプライン (1+2+3=6 ops) の実行に成功。"
            );

            let null_res = fidelogic_wasm_dummy_slot_eval_test(core::ptr::null(), 0);
            assert_eq!(
                null_res, 6,
                "空AAD指定でのダミー暗号演算パイプライン実行に成功。"
            );

            let overflow_res = fidelogic_wasm_dummy_slot_eval_test(aad.as_ptr(), usize::MAX);
            assert_eq!(
                overflow_res, 6,
                "isize::MAX超過時に空AADへ安全にフォールバックして実行に成功。"
            );
        }
    }

    #[cfg(any(test, feature = "ci-inspection"))]
    #[test]
    fn test_zeroize_test_export() {
        let mut buf = [0x55u8; 16];
        unsafe {
            fidelogic_wasm_zeroize_test(buf.as_mut_ptr(), buf.len());
            assert_eq!(buf, [0u8; 16], "指定バッファのゼロ消去に成功。");

            // NULLポインタや長さ0、isize::MAX超過時に未定義動作を起こさず安全にリターンすることを検証。
            fidelogic_wasm_zeroize_test(core::ptr::null_mut(), 16);
            fidelogic_wasm_zeroize_test(buf.as_mut_ptr(), 0);
            fidelogic_wasm_zeroize_test(buf.as_mut_ptr(), usize::MAX);
        }
    }

    #[test]
    fn test_ranges_overlap() {
        let buf = [0u8; 64];
        let p = buf.as_ptr();

        // 完全に分離している区間
        assert!(
            !ranges_overlap(p, 10, unsafe { p.add(10) }, 10),
            "隣接する区間は重複なし。"
        );
        assert!(
            !ranges_overlap(p, 10, unsafe { p.add(20) }, 10),
            "離れた区間は重複なし。"
        );

        // 一部重複している区間
        assert!(
            ranges_overlap(p, 15, unsafe { p.add(10) }, 10),
            "前方と後方が一部重複。"
        );
        assert!(
            ranges_overlap(unsafe { p.add(10) }, 10, p, 15),
            "後方と前方が一部重複。"
        );

        // 包含関係にある区間
        assert!(
            ranges_overlap(p, 30, unsafe { p.add(10) }, 10),
            "包含関係にある区間の重複検出。"
        );
        assert!(
            ranges_overlap(unsafe { p.add(10) }, 10, p, 30),
            "被包含関係にある区間の重複検出。"
        );

        // 同一区間
        assert!(
            ranges_overlap(p, 10, p, 10),
            "完全に同一のアドレス・長さでの重複検出。"
        );

        // 長さ0の場合は重複しない
        assert!(!ranges_overlap(p, 0, p, 10), "長さ0の区間は重複なし。");
        assert!(!ranges_overlap(p, 10, p, 0), "長さ0の区間は重複なし。");
        assert!(!ranges_overlap(p, 0, p, 0), "両方長さ0の区間は重複なし。");

        // saturating_add によるオーバーフロー耐性
        assert!(
            !ranges_overlap(p, 10, (usize::MAX - 5) as *const u8, 10),
            "usize::MAX境界付近の区間でもパニックせず重複なしを判定。"
        );
    }

    #[cfg(any(feature = "profile-lite", feature = "profile-vault"))]
    #[test]
    fn test_x25519_dh_aliasing() {
        let priv_a = [0x01u8; 32];
        let pub_b =
            fidelogic_core::x25519_basepoint_mul(&fidelogic_core::SecretBytes::new([0x02u8; 32]));
        let mut shared = [0u8; 32];

        unsafe {
            // secret_key と out_shared が重複している場合
            let res_secret_overlap = fidelogic_wasm_x25519_dh(
                shared.as_ptr(),
                pub_b.as_bytes().as_ptr(),
                shared.as_mut_ptr(),
            );
            assert_eq!(
                res_secret_overlap, 1,
                "秘密鍵と出力領域が重複している場合はエラーコード1を返却。"
            );

            // public_key と out_shared が重複している場合
            let res_public_overlap =
                fidelogic_wasm_x25519_dh(priv_a.as_ptr(), shared.as_ptr(), shared.as_mut_ptr());
            assert_eq!(
                res_public_overlap, 1,
                "公開鍵と出力領域が重複している場合はエラーコード1を返却。"
            );
        }
    }

    #[cfg(feature = "profile-vault")]
    #[test]
    fn test_kdf_derive_key_aliasing() {
        let mut buf = [0x42u8; 64];

        unsafe {
            // password と out が重複している場合
            let res_pw = fidelogic_wasm_kdf_derive_key(
                buf.as_ptr(),
                32,
                buf.as_ptr().add(48),
                16,
                buf.as_mut_ptr().add(16),
                32,
            );
            assert_eq!(
                res_pw, 1,
                "パスワードと出力領域が重複している場合はエラーコード1を返却。"
            );

            // salt と out が重複している場合
            let res_salt = fidelogic_wasm_kdf_derive_key(
                buf.as_ptr(),
                16,
                buf.as_ptr().add(20),
                16,
                buf.as_mut_ptr().add(16),
                32,
            );
            assert_eq!(
                res_salt, 1,
                "ソルトと出力領域が重複している場合はエラーコード1を返却。"
            );
        }
    }

    #[cfg(feature = "profile-vault")]
    #[test]
    fn test_vault_encrypt_decrypt_aliasing() {
        let key = [0x42u8; 32];
        let nonce = [0x24u8; 24];
        let aad = b"test-aad";
        let mut buffer = b"test-data-payload-longer-chunk".to_vec();
        let mut tag = [0u8; 16];

        unsafe {
            // encrypt: data と key の重複
            let res_key_overlap = fidelogic_wasm_vault_encrypt(
                1,
                buffer.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                buffer.as_mut_ptr(),
                buffer.len(),
                tag.as_mut_ptr(),
            );
            assert_eq!(
                res_key_overlap, 1,
                "データ領域と鍵領域が重複している暗号化はエラーコード1を返却。"
            );

            // encrypt: data と nonce の重複
            let res_nonce_overlap = fidelogic_wasm_vault_encrypt(
                1,
                key.as_ptr(),
                buffer.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                buffer.as_mut_ptr(),
                buffer.len(),
                tag.as_mut_ptr(),
            );
            assert_eq!(
                res_nonce_overlap, 1,
                "データ領域とノンス領域が重複している暗号化はエラーコード1を返却。"
            );

            // encrypt: tag_out と data の重複
            let res_tag_data_overlap = fidelogic_wasm_vault_encrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                buffer.as_mut_ptr(),
                buffer.len(),
                buffer.as_mut_ptr(),
            );
            assert_eq!(
                res_tag_data_overlap, 1,
                "データ領域と出力タグ領域が重複している暗号化はエラーコード1を返却。"
            );

            // decrypt: data と tag の重複
            let res_dec_tag_overlap = fidelogic_wasm_vault_decrypt(
                1,
                key.as_ptr(),
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                buffer.as_mut_ptr(),
                buffer.len(),
                buffer.as_ptr(),
            );
            assert_eq!(
                res_dec_tag_overlap, 1,
                "データ領域とタグ領域が重複している復号はエラーコード1を返却。"
            );
        }
    }
}
