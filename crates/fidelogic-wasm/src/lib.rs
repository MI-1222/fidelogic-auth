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
    let safe_a_ptr = if a_non_null {
        a_ptr
    } else {
        ZERO_BLOCK.as_ptr()
    };
    let safe_b_ptr = if b_non_null {
        b_ptr
    } else {
        ZERO_BLOCK.as_ptr()
    };
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
/// また、非NULLの `out_suite_id` および `out_epoch_id` は、それぞれ 1 バイトおよび
/// 8 バイトの書き込み可能メモリ領域を指している必要がある(`out_epoch_id` は非アライン可)。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_header_parse(
    header_bytes_ptr: *const u8,
    len: usize,
    out_suite_id: *mut u8,
    out_epoch_id: *mut u64,
) -> u32 {
    if header_bytes_ptr.is_null() || len < fidelogic_core::tlv::VAULT_HEADER_LEN {
        return 1;
    }
    let slice = unsafe { core::slice::from_raw_parts(header_bytes_ptr, len) };
    match fidelogic_core::tlv::deserialize_header(slice) {
        Ok((header, _)) => {
            if !out_suite_id.is_null() {
                unsafe { *out_suite_id = header.suite_id };
            }
            if !out_epoch_id.is_null() {
                // JS/Wasm 側のパック済みバッファ等からの非アラインポインタ渡しでも未定義動作にならないよう書き込む。
                unsafe { core::ptr::write_unaligned(out_epoch_id, header.epoch_id) };
            }
            0
        }
        Err(_) => 2,
    }
}

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
        return 1;
    }
    let key_arr = unsafe { &*(secret_key_ptr as *const [u8; 32]) };
    let secret = fidelogic_core::SecretBytes::new(*key_arr);
    let public = unsafe { &*(public_key_ptr as *const [u8; 32]) };
    match fidelogic_core::x25519_diffie_hellman(&secret, public) {
        Ok(shared) => {
            let out_slice = unsafe { core::slice::from_raw_parts_mut(out_shared_ptr, 32) };
            out_slice.copy_from_slice(shared.as_bytes());
            0
        }
        Err(_) => 2,
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
    if password_ptr.is_null() || salt_ptr.is_null() || out_ptr.is_null() {
        return 1;
    }
    let password = unsafe { core::slice::from_raw_parts(password_ptr, password_len) };
    let salt = unsafe { core::slice::from_raw_parts(salt_ptr, salt_len) };
    let out = unsafe { core::slice::from_raw_parts_mut(out_ptr, out_len) };

    let wasm_params = fidelogic_core::Argon2Params::for_wasm();
    let params = match fidelogic_core::Argon2Params::custom(
        wasm_params.m_cost(),
        wasm_params.t_cost(),
        wasm_params.p_cost(),
        Some(out_len),
    ) {
        Ok(p) => p,
        Err(_) => return 2,
    };

    match params.derive_key(password, salt, out) {
        Ok(()) => 0,
        Err(_) => 3,
    }
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
    if key_ptr.is_null() || nonce_ptr.is_null() || tag_out_ptr.is_null() {
        return 1;
    }
    if data_len > 0 && data_ptr.is_null() {
        return 1;
    }
    if aad_len > 0 && aad_ptr.is_null() {
        return 1;
    }
    let suite = match fidelogic_core::CipherSuiteId::from_u8(suite_id) {
        Ok(s) => s,
        Err(_) => return 2,
    };
    let key = unsafe { &*(key_ptr as *const [u8; fidelogic_core::KEY_LEN]) };
    let cipher = fidelogic_core::VaultCipher::new(suite, key);

    let nonce = unsafe { core::slice::from_raw_parts(nonce_ptr, nonce_len) };
    let aad = if aad_len > 0 {
        unsafe { core::slice::from_raw_parts(aad_ptr, aad_len) }
    } else {
        &[]
    };
    let data = if data_len > 0 {
        unsafe { core::slice::from_raw_parts_mut(data_ptr, data_len) }
    } else {
        &mut []
    };

    match cipher.encrypt_in_place_detached(nonce, aad, data) {
        Ok(tag) => {
            let tag_out =
                unsafe { core::slice::from_raw_parts_mut(tag_out_ptr, fidelogic_core::TAG_LEN) };
            tag_out.copy_from_slice(&tag);
            0
        }
        Err(_) => 3,
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
    if key_ptr.is_null() || nonce_ptr.is_null() || tag_ptr.is_null() {
        return 1;
    }
    if data_len > 0 && data_ptr.is_null() {
        return 1;
    }
    if aad_len > 0 && aad_ptr.is_null() {
        return 1;
    }
    let suite = match fidelogic_core::CipherSuiteId::from_u8(suite_id) {
        Ok(s) => s,
        Err(_) => return 2,
    };
    let key = unsafe { &*(key_ptr as *const [u8; fidelogic_core::KEY_LEN]) };
    let cipher = fidelogic_core::VaultCipher::new(suite, key);

    let nonce = unsafe { core::slice::from_raw_parts(nonce_ptr, nonce_len) };
    let aad = if aad_len > 0 {
        unsafe { core::slice::from_raw_parts(aad_ptr, aad_len) }
    } else {
        &[]
    };
    let data = if data_len > 0 {
        unsafe { core::slice::from_raw_parts_mut(data_ptr, data_len) }
    } else {
        &mut []
    };
    let tag = unsafe { core::slice::from_raw_parts(tag_ptr, fidelogic_core::TAG_LEN) };

    match cipher.decrypt_in_place_detached(nonce, aad, data, tag) {
        Ok(()) => 0,
        Err(_) => 3,
    }
}

#[cfg(feature = "profile-vault")]
/// Vault 全体のTLVデシリアライズ検証の外部C ABIエクスポート関数。
///
/// # Safety
/// 各ポインタは指定された長さの有効なメモリ領域を指していること。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_vault_deserialize(bytes_ptr: *const u8, len: usize) -> u32 {
    if bytes_ptr.is_null() || len == 0 {
        return 1;
    }
    let bytes = unsafe { core::slice::from_raw_parts(bytes_ptr, len) };
    match fidelogic_core::tlv::deserialize(bytes) {
        Ok((_vault, _)) => 0,
        Err(_) => 3,
    }
}

#[cfg(feature = "profile-vault")]
/// サイズゲート計測用アンカー: LTOによる `tlv::serialize` のデッドコード除去を抑止する内部検証用スタブ。
///
/// 本番API([`fidelogic_wasm_vault_deserialize`])から再シリアライズ副作用を分離するために独立させており、
/// 通常運用からの呼び出しは想定しない。
///
/// # Safety
/// 各ポインタは指定された長さの有効なメモリ領域を指していること。
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fidelogic_wasm_size_anchor(bytes_ptr: *const u8, len: usize) -> u32 {
    if bytes_ptr.is_null() || len == 0 {
        return 1;
    }
    let bytes = unsafe { core::slice::from_raw_parts(bytes_ptr, len) };
    match fidelogic_core::tlv::deserialize(bytes) {
        Ok((vault, _)) => match fidelogic_core::tlv::serialize(&vault) {
            Ok(_) => 0,
            Err(_) => 2,
        },
        Err(_) => 3,
    }
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

    #[test]
    fn test_x25519_dh() {
        let priv_a = [0x01u8; 32];
        let pub_b =
            fidelogic_core::x25519_basepoint_mul(&fidelogic_core::SecretBytes::new([0x02u8; 32]));
        let mut shared = [0u8; 32];

        unsafe {
            let res =
                fidelogic_wasm_x25519_dh(priv_a.as_ptr(), pub_b.as_ptr(), shared.as_mut_ptr());
            assert_eq!(res, 0, "X25519 DH鍵共有に成功。");
            assert_ne!(shared, [0u8; 32], "非ゼロの共有秘密の導出に成功。");
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
        }
    }
}
