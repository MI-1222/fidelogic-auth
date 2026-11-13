//! # PRECIS プロファイル正準化エンジン (RFC 7564 / RFC 8265)。
//!
//! 形式仕様 `proofs/Theories/PrecisProfile.v` に対応し、
//! 禁止コードポイント判定、純粋関数型 Case Folding、正準合成 (NFC)、
//! `UsernameCaseMapped` および `OpaqueString` プロファイル正準化を提供する。

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};

#[cfg(feature = "alloc")]
use crate::error::PrecisError;
#[cfg(feature = "alloc")]
use crate::zeroize::{SecretVec, volatile_zeroize};
#[cfg(feature = "alloc")]
use zeroize::Zeroizing;

/// Unicode コードポイントの最大有効値 (`U+10FFFF`)。
pub const UNICODE_MAX_CODE_POINT: u32 = 0x10_FFFF;

/// ハングル Jamo 初声ベースコードポイント (`U+1100`)。
const HANGUL_L_BASE: u32 = 0x1100;

/// ハングル Jamo 初声上限コードポイント (`U+1112`)。
const HANGUL_L_END: u32 = 0x1112;

/// ハングル Jamo 中声ベースコードポイント (`U+1161`)。
const HANGUL_V_BASE: u32 = 0x1161;

/// ハングル Jamo 中声上限コードポイント (`U+1175`)。
const HANGUL_V_END: u32 = 0x1175;

/// ハングル Jamo 終声ベースコードポイント (`U+11A7`, `TCount` 計算基準)。
const HANGUL_T_BASE: u32 = 0x11A7;

/// ハングル Jamo 終声下限コードポイント (`U+11A8`)。
const HANGUL_T_START: u32 = 0x11A8;

/// ハングル Jamo 終声上限コードポイント (`U+11C2`)。
const HANGUL_T_END: u32 = 0x11C2;

/// ハングル音節ベースコードポイント (`U+AC00`)。
const HANGUL_S_BASE: u32 = 0xAC00;

/// ハングル LV 音節上限コードポイント (`44032 + 18 * 588 + 20 * 28 = 55176`)。
const HANGUL_LV_END: u32 = 55_176;

/// ハングル終声総数 (`TCount = 28`)。
const HANGUL_T_COUNT: u32 = 28;

/// ハングル中声×終声総数 (`NCount = 21 * 28 = 588`)。
const HANGUL_N_COUNT: u32 = 588;

/// 閉区間 `[low, high]` にコードポイント `cp` が含まれるかを判定する純粋関数。
#[inline]
#[must_use]
pub const fn in_range(low: u32, high: u32, cp: u32) -> bool {
    low <= cp && cp <= high
}

/// ASCII 制御文字 (`0x00..=0x1F`, `0x7F`) であるかを判定する。
#[inline]
#[must_use]
pub const fn is_ascii_control(cp: u32) -> bool {
    cp <= 0x1F || cp == 0x7F
}

/// 非 ASCII 制御文字 (`0x80..=0x9F`) であるかを判定する。
#[inline]
#[must_use]
pub const fn is_non_ascii_control(cp: u32) -> bool {
    in_range(0x80, 0x9F, cp)
}

/// ASCII 空白文字 (`0x20`) であるかを判定する。
#[inline]
#[must_use]
pub const fn is_space(cp: u32) -> bool {
    cp == 0x20
}

/// Unicode `Zs` (Space_Separator) カテゴリの文字であるかを判定する (RFC 8265 Section 4.2.2)。
///
/// 対象コードポイント:
/// - `0x0020` (SPACE)
/// - `0x00A0` (NO-BREAK SPACE)
/// - `0x1680` (OGHAM SPACE MARK)
/// - `0x2000..=0x200A` (EN QUAD .. HAIR SPACE)
/// - `0x202F` (NARROW NO-BREAK SPACE)
/// - `0x205F` (MEDIUM MATHEMATICAL SPACE)
/// - `0x3000` (IDEOGRAPHIC SPACE)
#[inline]
#[must_use]
pub const fn is_zs_space(cp: u32) -> bool {
    matches!(
        cp,
        0x0020 | 0x00A0 | 0x1680 | 0x2000..=0x200A | 0x202F | 0x205F | 0x3000
    )
}

/// Unicode `Zs` (Space_Separator) カテゴリの文字を ASCII 空白 (`0x0020`) にマッピングする (RFC 8265 Section 4.2.2)。
///
/// 対象外のコードポイントは変更せずそのまま返す。
#[inline]
#[must_use]
pub const fn map_zs_to_space(cp: u32) -> u32 {
    if is_zs_space(cp) { 0x0020 } else { cp }
}

/// Unicode サロゲートコードポイント (`0xD800..=0xDFFF`) であるかを判定する。
#[inline]
#[must_use]
pub const fn is_surrogate(cp: u32) -> bool {
    in_range(0xD800, 0xDFFF, cp)
}

/// 私用領域 (Private Use Area: BMP, Plane 15, Plane 16) であるかを判定する。
#[inline]
#[must_use]
pub const fn is_private_use(cp: u32) -> bool {
    in_range(0xE000, 0xF8FF, cp)
        || in_range(0xF_0000, 0xF_FFFD, cp)
        || in_range(0x10_0000, 0x10_FFFD, cp)
}

/// Unicode 非文字 (Noncharacters: `0xFDD0..=0xFDEF` および各面末尾2文字) であるかを判定する。
#[inline]
#[must_use]
pub const fn is_noncharacter(cp: u32) -> bool {
    in_range(0xFDD0, 0xFDEF, cp)
        || (cp <= UNICODE_MAX_CODE_POINT
            && ((cp % 0x1_0000) == 0xFFFE || (cp % 0x1_0000) == 0xFFFF))
}

/// Unicode 有効範囲外 (`cp > 0x10FFFF`) であるかを判定する。
#[inline]
#[must_use]
pub const fn is_out_of_bounds(cp: u32) -> bool {
    cp > UNICODE_MAX_CODE_POINT
}

/// `FreeformClass` (`OpaqueString`) における総合禁止コードポイント判定を行う。
///
/// `proofs/Theories/PrecisProfile.v` のモデルに対応し、
/// RFC 7564 (RFC 8264) Section 4.3.3 および RFC 8265 Section 4.2 に基づき、
/// ASCII 空白 (`0x20`) を許可しつつ、範囲外文字、ASCII/非ASCII制御文字、
/// サロゲート、私用領域、非文字を禁止する。
#[inline]
#[must_use]
pub const fn is_opaque_disallowed_cp(cp: u32) -> bool {
    is_out_of_bounds(cp)
        || is_ascii_control(cp)
        || is_non_ascii_control(cp)
        || is_surrogate(cp)
        || is_private_use(cp)
        || is_noncharacter(cp)
}

/// `IdentifierClass` (`UsernameCaseMapped`) における総合禁止コードポイント判定を行う。
///
/// `proofs/Theories/PrecisProfile.v` のモデルに対応し、
/// RFC 7564 (RFC 8264) Section 4.2.3 および RFC 8265 Section 3.3 に基づき、
/// `FreeformClass` の禁止文字に加えて ASCII 空白 (`0x20`) を禁止する。
#[inline]
#[must_use]
pub const fn is_disallowed_cp(cp: u32) -> bool {
    is_opaque_disallowed_cp(cp) || is_space(cp)
}

/// コードポイント列のすべての要素が `IdentifierClass` で許可されているかを判定する。
#[inline]
#[must_use]
pub fn all_allowed(cps: &[u32]) -> bool {
    PrecisProfile::UsernameCaseMapped.all_allowed(cps)
}

/// コードポイント列を先頭から走査し、最初に検出された禁止コードポイントを返す。
#[inline]
#[must_use]
pub fn find_disallowed_cp(cps: &[u32]) -> Option<u32> {
    PrecisProfile::UsernameCaseMapped.find_disallowed_cp(cps)
}

/// コードポイント列のすべての要素が `FreeformClass` (`OpaqueString`) で許可されているかを判定する。
#[inline]
#[must_use]
pub fn all_opaque_allowed(cps: &[u32]) -> bool {
    PrecisProfile::OpaqueString.all_allowed(cps)
}

/// コードポイント列を先頭から走査し、`FreeformClass` で最初に検出された禁止コードポイントを返す。
#[inline]
#[must_use]
pub fn find_opaque_disallowed_cp(cps: &[u32]) -> Option<u32> {
    PrecisProfile::OpaqueString.find_disallowed_cp(cps)
}

/// 単一コードポイントに対する純粋関数型 Case Folding (大文字小文字マッピング) を適用する。
///
/// `PrecisProfile.v` (`precis_fold_cp`) に一致し、以下の大文字領域を小文字 (`+ 32`) へ写像する。
/// - ASCII 英大文字 (`0x0041..=0x005A`)。
/// - Latin-1 拡張大文字 (`0x00C0..=0x00D6`, `0x00D8..=0x00DE`)。
/// - ギリシャ文字大文字 (`0x0391..=0x03A1`, `0x03A3..=0x03AB`)。
/// - キリル文字大文字 (`0x0410..=0x042F`)。
#[inline]
#[must_use]
pub const fn precis_fold_cp(cp: u32) -> u32 {
    if in_range(0x0041, 0x005A, cp)
        || in_range(0x00C0, 0x00D6, cp)
        || in_range(0x00D8, 0x00DE, cp)
        || in_range(0x0391, 0x03A1, cp)
        || in_range(0x03A3, 0x03AB, cp)
        || in_range(0x0410, 0x042F, cp)
    {
        cp + 0x0020
    } else {
        cp
    }
}

/// 単一の Unicode スカラー値 (`char`) に対して Case Folding を適用する。
#[inline]
#[must_use]
pub const fn precis_fold_char(ch: char) -> char {
    let folded = precis_fold_cp(ch as u32);
    match char::from_u32(folded) {
        Some(c) => c,
        None => ch,
    }
}

/// コードポイント列全体に対して Case Folding を適用する。
#[cfg(feature = "alloc")]
#[must_use]
pub fn precis_fold_string(cps: &[u32]) -> Vec<u32> {
    let mut out = Zeroizing::new(Vec::with_capacity(cps.len()));
    out.extend(cps.iter().copied().map(precis_fold_cp));
    core::mem::take(&mut *out)
}

/// ハングル音節合成 (`Jamo L + V -> LV`) を検証付きで計算する。
///
/// 初声 `l` (`U+1100..=U+1112`) と中声 `v` (`U+1161..=U+1175`) が妥当な範囲内にある場合、
/// 合成されたハングル LV 音節コードポイント (`U+AC00..=U+D7A3` のうち LV 音節) を返す。
/// いずれかのコードポイントが Jamo 範囲外の場合は `None` を返す。
#[inline]
#[must_use]
pub const fn compose_hangul_syllable(l: u32, v: u32) -> Option<u32> {
    if !in_range(HANGUL_L_BASE, HANGUL_L_END, l) || !in_range(HANGUL_V_BASE, HANGUL_V_END, v) {
        return None;
    }
    let l_idx = l - HANGUL_L_BASE;
    let v_idx = v - HANGUL_V_BASE;
    Some(HANGUL_S_BASE + l_idx * HANGUL_N_COUNT + v_idx * HANGUL_T_COUNT)
}

/// ハングル音節終声合成 (`LV + T -> LVT`) を検証付きで計算する。
///
/// 音節 `lv` が有効な LV 音節範囲内 (`U+AC00..=U+D788` かつ `(lv - SBase) % 28 == 0`) であり、
/// 終声 `t` が終声 Jamo 範囲内 (`U+11A8..=U+11C2`) にある場合、
/// 合成されたハングル LVT 音節コードポイントを返す。
/// 入力が範囲外または無効な組み合わせの場合は `None` を返す。
#[inline]
#[must_use]
pub const fn compose_hangul_trailing(lv: u32, t: u32) -> Option<u32> {
    if !in_range(HANGUL_S_BASE, HANGUL_LV_END, lv)
        || !((lv - HANGUL_S_BASE).is_multiple_of(HANGUL_T_COUNT))
        || !in_range(HANGUL_T_START, HANGUL_T_END, t)
    {
        return None;
    }
    Some(lv + (t - HANGUL_T_BASE))
}

/// 単一ペアに対する Unicode 正準合成 (Canonical Composition) を適用する。
///
/// `PrecisProfile.v` (`compose_pair`) と同一の合成規則に従い、
/// Latin 基底文字 (`A/a`, `C/c`, `E/e`, `I/i`, `N/n`, `O/o`, `U/u`, `Y/y`) +
/// 結合ダイアクリティカルマーク、およびハングル Jamo (`L + V`, `LV + T`) を合成する。
///
/// 有界モデルとして、対象となる合成ペアは本関数に定義された組のみに限定される。
#[must_use]
pub const fn compose_pair(c1: u32, c2: u32) -> Option<u32> {
    match (c1, c2) {
        // Latin 'A' (0x0041) / 'a' (0x0061)。
        (0x0041, 0x0300) => Some(0x00C0),
        (0x0041, 0x0301) => Some(0x00C1),
        (0x0041, 0x0302) => Some(0x00C2),
        (0x0041, 0x0303) => Some(0x00C3),
        (0x0041, 0x0308) => Some(0x00C4),
        (0x0041, 0x030A) => Some(0x00C5),
        (0x0061, 0x0300) => Some(0x00E0),
        (0x0061, 0x0301) => Some(0x00E1),
        (0x0061, 0x0302) => Some(0x00E2),
        (0x0061, 0x0303) => Some(0x00E3),
        (0x0061, 0x0308) => Some(0x00E4),
        (0x0061, 0x030A) => Some(0x00E5),
        // Latin 'C' (0x0043) / 'c' (0x0063)。
        (0x0043, 0x0327) => Some(0x00C7),
        (0x0063, 0x0327) => Some(0x00E7),
        // Latin 'E' (0x0045) / 'e' (0x0065)。
        (0x0045, 0x0300) => Some(0x00C8),
        (0x0045, 0x0301) => Some(0x00C9),
        (0x0045, 0x0302) => Some(0x00CA),
        (0x0045, 0x0308) => Some(0x00CB),
        (0x0065, 0x0300) => Some(0x00E8),
        (0x0065, 0x0301) => Some(0x00E9),
        (0x0065, 0x0302) => Some(0x00EA),
        (0x0065, 0x0308) => Some(0x00EB),
        // Latin 'I' (0x0049) / 'i' (0x0069)。
        (0x0049, 0x0300) => Some(0x00CC),
        (0x0049, 0x0301) => Some(0x00CD),
        (0x0049, 0x0302) => Some(0x00CE),
        (0x0049, 0x0308) => Some(0x00CF),
        (0x0069, 0x0300) => Some(0x00EC),
        (0x0069, 0x0301) => Some(0x00ED),
        (0x0069, 0x0302) => Some(0x00EE),
        (0x0069, 0x0308) => Some(0x00EF),
        // Latin 'N' (0x004E) / 'n' (0x006E)。
        (0x004E, 0x0303) => Some(0x00D1),
        (0x006E, 0x0303) => Some(0x00F1),
        // Latin 'O' (0x004F) / 'o' (0x006F)。
        (0x004F, 0x0300) => Some(0x00D2),
        (0x004F, 0x0301) => Some(0x00D3),
        (0x004F, 0x0302) => Some(0x00D4),
        (0x004F, 0x0303) => Some(0x00D5),
        (0x004F, 0x0308) => Some(0x00D6),
        (0x006F, 0x0300) => Some(0x00F2),
        (0x006F, 0x0301) => Some(0x00F3),
        (0x006F, 0x0302) => Some(0x00F4),
        (0x006F, 0x0303) => Some(0x00F5),
        (0x006F, 0x0308) => Some(0x00F6),
        // Latin 'U' (0x0055) / 'u' (0x0075)。
        (0x0055, 0x0300) => Some(0x00D9),
        (0x0055, 0x0301) => Some(0x00DA),
        (0x0055, 0x0302) => Some(0x00DB),
        (0x0055, 0x0308) => Some(0x00DC),
        (0x0075, 0x0300) => Some(0x00F9),
        (0x0075, 0x0301) => Some(0x00FA),
        (0x0075, 0x0302) => Some(0x00FB),
        (0x0075, 0x0308) => Some(0x00FC),
        // Latin 'Y' (0x0059) / 'y' (0x0079)。
        (0x0059, 0x0301) => Some(0x00DD),
        (0x0079, 0x0301) => Some(0x00FD),
        (0x0079, 0x0308) => Some(0x00FF),
        // ハングル L + V および LV + T。
        _ if in_range(HANGUL_L_BASE, HANGUL_L_END, c1)
            && in_range(HANGUL_V_BASE, HANGUL_V_END, c2) =>
        {
            compose_hangul_syllable(c1, c2)
        }
        _ if in_range(HANGUL_S_BASE, HANGUL_LV_END, c1)
            && (c1 - HANGUL_S_BASE).is_multiple_of(HANGUL_T_COUNT)
            && in_range(HANGUL_T_START, HANGUL_T_END, c2) =>
        {
            compose_hangul_trailing(c1, c2)
        }
        _ => None,
    }
}

/// コードポイント列に対して Unicode 正準合成 (NFC) を適用する。
///
/// `PrecisProfile.v` (`precis_nfc_normalize`) に一致する。
/// 対象となる合成ペアは [`compose_pair`] 定義分に限定され、
/// 連続する結合文字の正準結合クラス (CCC) 順による並べ替えや NFD 再分解は、
/// 有界モデルの対象外であり未実装である。
#[cfg(feature = "alloc")]
#[must_use]
pub fn precis_nfc_normalize(cps: &[u32]) -> Vec<u32> {
    let mut out = Zeroizing::new(Vec::with_capacity(cps.len()));
    let mut idx = 0;

    while idx < cps.len() {
        let c1 = cps[idx];
        if idx + 1 >= cps.len() {
            out.push(c1);
            break;
        }

        let c2 = cps[idx + 1];
        if let Some(composed) = compose_pair(c1, c2) {
            if idx + 2 < cps.len()
                && let Some(composed_with_trailing) = compose_pair(composed, cps[idx + 2])
            {
                out.push(composed_with_trailing);
                idx += 3;
                continue;
            }
            out.push(composed);
            idx += 2;
        } else {
            out.push(c1);
            idx += 1;
        }
    }

    core::mem::take(&mut *out)
}

/// コードポイント列に対して `UsernameCaseMapped` プロファイル正準化 (RFC 8265 Section 3.3 形式モデル) を適用する。
///
/// `proofs/Theories/PrecisProfile.v` の仕様に一致する範囲
/// (限定 Case Folding、NFC 部分合成、および禁止文字検査; 幅マッピングおよび Bidi 規則は対象外) を実装する。
///
/// 処理手順を以下に示す。
/// 1. 空入力を拒絶 ([`PrecisError::EmptyInput`])。
/// 2. Case Folding (`precis_fold_string`) を適用。
/// 3. Unicode NFC 正規化 (`precis_nfc_normalize`) を適用。
/// 4. 禁止コードポイント検査 (`find_disallowed_cp`) を実施し、違反時は [`PrecisError::DisallowedCodePoint`] を返却。
///
/// # Errors
///
/// 入力が空であるか、正規化後に禁止コードポイントが含まれる場合は [`PrecisError`] を返す。
#[cfg(feature = "alloc")]
pub fn enforce_username_case_mapped_cps(cps: &[u32]) -> Result<Vec<u32>, PrecisError> {
    if cps.is_empty() {
        return Err(PrecisError::EmptyInput);
    }

    let folded = Zeroizing::new(precis_fold_string(cps));
    let mut normalized = Zeroizing::new(precis_nfc_normalize(&folded));
    if let Some(disallowed) = find_disallowed_cp(&normalized) {
        return Err(PrecisError::DisallowedCodePoint(disallowed));
    }

    Ok(core::mem::take(&mut *normalized))
}

/// `PrecisProfile.v` (`precis_username_case_mapped`) に対応する `Option` 返却ラッパー。
#[cfg(feature = "alloc")]
#[must_use]
pub fn precis_username_case_mapped(cps: &[u32]) -> Option<Vec<u32>> {
    enforce_username_case_mapped_cps(cps).ok()
}

/// UTF-8 文字列をコードポイント列へ変換してプロファイル正準化を適用し、UTF-8 文字列へ再構築する共通ヘルパー。
#[cfg(feature = "alloc")]
fn apply_str_profile<F>(input: &str, enforce_cps: F) -> Result<String, PrecisError>
where
    F: FnOnce(&[u32]) -> Result<Vec<u32>, PrecisError>,
{
    if input.is_empty() {
        return Err(PrecisError::EmptyInput);
    }

    let char_count = input.chars().count();
    let mut cps = Zeroizing::new(Vec::with_capacity(char_count));
    cps.extend(input.chars().map(|ch| ch as u32));
    let normalized = Zeroizing::new(enforce_cps(&cps)?);

    let mut out = Zeroizing::new(String::with_capacity(input.len()));
    for &cp in normalized.iter() {
        let ch = char::from_u32(cp).ok_or(PrecisError::DisallowedCodePoint(cp))?;
        out.push(ch);
    }

    Ok(core::mem::take(&mut *out))
}

/// UTF-8 文字列に対して `UsernameCaseMapped` プロファイル正準化 (RFC 8265 Section 3.3) を適用する。
///
/// # Errors
///
/// 入力が空文字列であるか、正規化後に禁止コードポイントが含まれる場合は [`PrecisError`] を返す。
#[cfg(feature = "alloc")]
pub fn username_case_mapped(input: &str) -> Result<String, PrecisError> {
    apply_str_profile(input, enforce_username_case_mapped_cps)
}

/// コードポイント列に対して `OpaqueString` プロファイル正準化 (RFC 8265 Section 4.2) を適用する。
///
/// 処理手順を以下に示す。
/// 1. 空入力を拒絶 ([`PrecisError::EmptyInput`])。
/// 2. RFC 8265 Section 4.2.2 に従い、Unicode `Zs` カテゴリ文字を ASCII 空白 (`0x0020`) にマッピング。
/// 3. Case Folding を行わずに Unicode NFC 正規化 (`precis_nfc_normalize`) を適用。
/// 4. `FreeformClass` 禁止コードポイント検査 (`find_opaque_disallowed_cp`) を実施し、
///    ASCII 空白 (`0x20`) を許可しつつ制御文字・サロゲート・私用領域・非文字等を
///    [`PrecisError::DisallowedCodePoint`] として拒絶する。
///
/// # Errors
///
/// 入力が空であるか、正規化後に `FreeformClass` の禁止コードポイントが含まれる場合は [`PrecisError`] を返す。
#[cfg(feature = "alloc")]
pub fn enforce_opaque_string_cps(cps: &[u32]) -> Result<Vec<u32>, PrecisError> {
    if cps.is_empty() {
        return Err(PrecisError::EmptyInput);
    }

    // RFC 8265 Section 4.2.2: 非 ASCII 空白文字 (Unicode Zs カテゴリ) が含まれる場合のみ
    // マッピング済みバッファを生成し、通常時は不要なアロケーションを回避する。
    let has_non_ascii_zs = cps.iter().any(|&cp| cp != 0x0020 && is_zs_space(cp));
    let mut normalized = Zeroizing::new(if has_non_ascii_zs {
        let mut mapped = Zeroizing::new(Vec::with_capacity(cps.len()));
        mapped.extend(cps.iter().copied().map(map_zs_to_space));
        precis_nfc_normalize(&mapped)
    } else {
        precis_nfc_normalize(cps)
    });

    if let Some(disallowed) = find_opaque_disallowed_cp(&normalized) {
        return Err(PrecisError::DisallowedCodePoint(disallowed));
    }

    Ok(core::mem::take(&mut *normalized))
}

/// `PrecisProfile.v` (`precis_opaque_string`) に対応する `Option` 返却ラッパー。
#[cfg(feature = "alloc")]
#[must_use]
pub fn precis_opaque_string(cps: &[u32]) -> Option<Vec<u32>> {
    enforce_opaque_string_cps(cps).ok()
}

/// UTF-8 文字列に対して `OpaqueString` プロファイル正準化 (RFC 8265 Section 4.2) を適用する。
///
/// 大文字・小文字の区別を保持し、非 ASCII 空白 (Unicode `Zs` カテゴリ) を ASCII 空白 (`0x20`) へマッピングしたうえで
/// Unicode NFC 正規化を適用し、制御文字・サロゲート・私用領域・非文字等の禁止コードポイントを拒絶する。
///
/// # Errors
///
/// 入力が空文字列であるか、正規化後に `FreeformClass` の禁止コードポイントが含まれる場合は [`PrecisError`] を返す。
#[cfg(feature = "alloc")]
pub fn opaque_string(input: &str) -> Result<String, PrecisError> {
    apply_str_profile(input, enforce_opaque_string_cps)
}

/// UTF-8 文字列に対して `OpaqueString` プロファイル正準化 (RFC 8265 Section 4.2) を適用し、
/// メモリ残留を防ぐセキュアバッファ [`SecretVec`] として正準化済み UTF-8 バイト列を返却する。
///
/// 中間コードポイントバッファ (`Vec<u32>`) および戻り値バッファは、
/// 正常終了・エラー返却時を問わず確実にゼロ消去され、平文のヒープ残留を防止する。
///
/// # Errors
///
/// 入力が空文字列であるか、正規化後に `FreeformClass` の禁止コードポイントが含まれる場合は [`PrecisError`] を返す。
#[cfg(feature = "alloc")]
pub fn opaque_string_secret(input: &str) -> Result<SecretVec, PrecisError> {
    if input.is_empty() {
        return Err(PrecisError::EmptyInput);
    }

    let char_count = input.chars().count();
    let mut cps = Zeroizing::new(Vec::with_capacity(char_count));
    cps.extend(input.chars().map(|ch| ch as u32));
    let normalized = Zeroizing::new(enforce_opaque_string_cps(&cps)?);

    let mut secret_out = SecretVec::with_capacity(input.len());
    let mut utf8_buf = [0u8; 4];
    for &cp in normalized.iter() {
        let ch = char::from_u32(cp).ok_or_else(|| {
            secret_out.clear();
            volatile_zeroize(&mut utf8_buf);
            PrecisError::DisallowedCodePoint(cp)
        })?;
        let encoded = ch.encode_utf8(&mut utf8_buf);
        secret_out.extend_from_slice(encoded.as_bytes());
    }
    volatile_zeroize(&mut utf8_buf);

    Ok(secret_out)
}

/// PRECIS プロファイル正準化の種別を表す列挙型。
///
/// RFC 8265 で規定される `UsernameCaseMapped` (Section 3.3) および
/// `OpaqueString` (Section 4.2) の正準化戦略を表現する。
/// 列挙型のメソッドを経由してゼロコスト静的ディスパッチによる一貫した正準化インターフェースを提供する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrecisProfile {
    /// ユーザー名用プロファイル (`IdentifierClass` + Case Folding + NFC)。
    UsernameCaseMapped,
    /// パスワード・暗号シークレット用プロファイル (`FreeformClass` + 大小文字維持 + NFC)。
    OpaqueString,
}

impl PrecisProfile {
    /// プロファイルの識別名文字列を返す。
    #[inline]
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::UsernameCaseMapped => "UsernameCaseMapped",
            Self::OpaqueString => "OpaqueString",
        }
    }

    /// 対象プロファイルにおいて指定コードポイントが禁止文字であるかを判定する。
    #[inline]
    #[must_use]
    pub const fn is_disallowed_cp(self, cp: u32) -> bool {
        match self {
            Self::UsernameCaseMapped => is_disallowed_cp(cp),
            Self::OpaqueString => is_opaque_disallowed_cp(cp),
        }
    }

    /// コードポイント列のすべての要素が対象プロファイルで許可されているかを判定する。
    #[inline]
    #[must_use]
    pub fn all_allowed(self, cps: &[u32]) -> bool {
        self.find_disallowed_cp(cps).is_none()
    }

    /// コードポイント列を走査し、対象プロファイルで最初に検出された禁止コードポイントを返す。
    #[inline]
    #[must_use]
    pub fn find_disallowed_cp(self, cps: &[u32]) -> Option<u32> {
        cps.iter().copied().find(|&cp| self.is_disallowed_cp(cp))
    }

    /// コードポイント列に対して対象プロファイルの正準化を適用する。
    ///
    /// # Errors
    ///
    /// 入力が空であるか、正規化後に禁止コードポイントが含まれる場合は [`PrecisError`] を返す。
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn enforce_cps(self, cps: &[u32]) -> Result<Vec<u32>, PrecisError> {
        match self {
            Self::UsernameCaseMapped => enforce_username_case_mapped_cps(cps),
            Self::OpaqueString => enforce_opaque_string_cps(cps),
        }
    }

    /// `proofs/Theories/PrecisProfile.v` の仕様に対応する `Option` 返却ラッパー。
    #[cfg(feature = "alloc")]
    #[inline]
    #[must_use]
    pub fn precis_cps(self, cps: &[u32]) -> Option<Vec<u32>> {
        self.enforce_cps(cps).ok()
    }

    /// UTF-8 文字列に対して対象プロファイルの正準化を適用する。
    ///
    /// # Errors
    ///
    /// 入力が空文字列であるか、正規化後に禁止コードポイントが含まれる場合は [`PrecisError`] を返す。
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn enforce_str(self, input: &str) -> Result<String, PrecisError> {
        match self {
            Self::UsernameCaseMapped => username_case_mapped(input),
            Self::OpaqueString => opaque_string(input),
        }
    }

    /// UTF-8 文字列に対して対象プロファイルの正準化を適用し、秘密情報保護型 [`SecretVec`] として返却する。
    ///
    /// # Errors
    ///
    /// 入力が空文字列であるか、正規化後に禁止コードポイントが含まれる場合は [`PrecisError`] を返す。
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn enforce_str_secret(self, input: &str) -> Result<SecretVec, PrecisError> {
        match self {
            Self::UsernameCaseMapped => {
                let s = username_case_mapped(input)?;
                Ok(SecretVec::from_slice(s.as_bytes()))
            }
            Self::OpaqueString => opaque_string_secret(input),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn test_disallowed_cp_boundaries() {
        // ASCII 制御文字 (0x00..=0x1F, 0x7F)。
        assert!(is_ascii_control(0x00));
        assert!(is_ascii_control(0x1F));
        assert!(!is_ascii_control(0x20));
        assert!(!is_ascii_control(0x7E));
        assert!(is_ascii_control(0x7F));
        assert!(!is_ascii_control(0x80));

        // 非 ASCII 制御文字 (0x80..=0x9F)。
        assert!(is_non_ascii_control(0x80));
        assert!(is_non_ascii_control(0x9F));
        assert!(!is_non_ascii_control(0xA0));

        // ASCII 空白 (0x20)。
        assert!(is_space(0x20));
        assert!(!is_space(0x21));

        // サロゲート (0xD800..=0xDFFF)。
        assert!(!is_surrogate(0xD7FF));
        assert!(is_surrogate(0xD800));
        assert!(is_surrogate(0xDFFF));
        assert!(!is_surrogate(0xE000));

        // 私用領域 (PUA)。
        assert!(is_private_use(0xE000));
        assert!(is_private_use(0xF8FF));
        assert!(!is_private_use(0xF900));
        assert!(!is_private_use(0xE_FFFF));
        assert!(is_private_use(0xF_0000));
        assert!(is_private_use(0xF_FFFD));
        assert!(!is_private_use(0xF_FFFE));
        assert!(is_private_use(0x10_0000));
        assert!(is_private_use(0x10_FFFD));
        assert!(!is_private_use(0x10_FFFE));

        // 非文字 (Noncharacters)。
        assert!(!is_noncharacter(0xFDCF));
        assert!(is_noncharacter(0xFDD0));
        assert!(is_noncharacter(0xFDEF));
        assert!(!is_noncharacter(0xFDF0));
        assert!(is_noncharacter(0xFFFE));
        assert!(is_noncharacter(0xFFFF));
        assert!(is_noncharacter(0x1_FFFE));
        assert!(is_noncharacter(0x1_FFFF));
        assert!(is_noncharacter(0x10_FFFE));
        assert!(is_noncharacter(0x10_FFFF));

        // 有効範囲外。
        assert!(!is_out_of_bounds(UNICODE_MAX_CODE_POINT));
        assert!(is_out_of_bounds(UNICODE_MAX_CODE_POINT + 1));
        assert!(is_out_of_bounds(u32::MAX));

        // 総合判定。
        assert!(is_disallowed_cp(0x00));
        assert!(is_disallowed_cp(0x20));
        assert!(is_disallowed_cp(0x7F));
        assert!(is_disallowed_cp(0x80));
        assert!(is_disallowed_cp(0xD800));
        assert!(is_disallowed_cp(0xE000));
        assert!(is_disallowed_cp(0xFDD0));
        assert!(is_disallowed_cp(0xFFFF));
        assert!(is_disallowed_cp(0x11_0000));
        assert!(!is_disallowed_cp(b'a' as u32));
        assert!(!is_disallowed_cp(0x3042)); // 'あ'。
    }

    #[test]
    fn test_case_folding_boundaries() {
        // ASCII 境界。
        assert_eq!(precis_fold_cp(b'@' as u32), b'@' as u32);
        assert_eq!(precis_fold_cp(b'A' as u32), b'a' as u32);
        assert_eq!(precis_fold_cp(b'Z' as u32), b'z' as u32);
        assert_eq!(precis_fold_cp(b'[' as u32), b'[' as u32);

        // Latin-1 境界 (0xD7 '×' は対象外)。
        assert_eq!(precis_fold_cp(0x00C0), 0x00E0);
        assert_eq!(precis_fold_cp(0x00D6), 0x00F6);
        assert_eq!(precis_fold_cp(0x00D7), 0x00D7);
        assert_eq!(precis_fold_cp(0x00D8), 0x00F8);
        assert_eq!(precis_fold_cp(0x00DE), 0x00FE);
        assert_eq!(precis_fold_cp(0x00DF), 0x00DF);

        // ギリシャ文字境界 (0x03A2 は未割り当てのため対象外)。
        assert_eq!(precis_fold_cp(0x0391), 0x03B1);
        assert_eq!(precis_fold_cp(0x03A1), 0x03C1);
        assert_eq!(precis_fold_cp(0x03A2), 0x03A2);
        assert_eq!(precis_fold_cp(0x03A3), 0x03C3);
        assert_eq!(precis_fold_cp(0x03AB), 0x03CB);

        // キリル文字境界。
        assert_eq!(precis_fold_cp(0x0410), 0x0430);
        assert_eq!(precis_fold_cp(0x042F), 0x044F);

        // char 単位変換。
        assert_eq!(precis_fold_char('A'), 'a');
        assert_eq!(precis_fold_char('É'), 'é');
        assert_eq!(precis_fold_char('Σ'), 'σ');
        assert_eq!(precis_fold_char('И'), 'и');
        assert_eq!(precis_fold_char('×'), '×');
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_precis_profile_v_username_golden_vectors() {
        // PrecisProfile.v の precis_golden_suite (tc_expected_user) と全件一致を検証。
        let cases: &[(&[u32], Option<&[u32]>)] = &[
            (&[85, 115, 101, 114], Some(&[117, 115, 101, 114])),
            (&[85, 83, 69, 82], Some(&[117, 115, 101, 114])),
            (&[117, 115, 101, 114], Some(&[117, 115, 101, 114])),
            (&[927, 931], Some(&[959, 963])),
            (&[1048, 1074, 1072, 1085], Some(&[1080, 1074, 1072, 1085])),
            (&[201], Some(&[233])),
            (&[117, 115, 101, 114, 32, 110, 97, 109, 101], None),
            (&[], None),
            (&[0], None),
            (&[9], None),
            (&[55296], None),
            (&[57344], None),
            (&[65535], None),
            (&[64976], None),
            (&[101, 769], Some(&[233])),
            (&[65, 776], Some(&[228])),
            (&[99, 807], Some(&[231])),
            (&[4352, 4449], Some(&[44032])),
            (&[4352, 4449, 4520], Some(&[44033])),
            (&[44032, 4520], Some(&[44033])),
        ];

        for &(input, expected) in cases {
            let actual = precis_username_case_mapped(input);
            assert_eq!(
                actual.as_deref(),
                expected,
                "PrecisProfile.v のゴールデンベクタ {input:?} が一致することを検証。"
            );
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_username_case_mapped_str_api() {
        assert_eq!(username_case_mapped("User"), Ok(String::from("user")));
        assert_eq!(username_case_mapped("USER"), Ok(String::from("user")));
        assert_eq!(username_case_mapped("ΟΣ"), Ok(String::from("οσ")));
        assert_eq!(username_case_mapped("Иван"), Ok(String::from("иван")));
        assert_eq!(username_case_mapped("É"), Ok(String::from("é")));
        assert_eq!(username_case_mapped("A\u{0308}"), Ok(String::from("ä")));
        assert_eq!(
            username_case_mapped("\u{1100}\u{1161}\u{11A8}"),
            Ok(String::from("각"))
        );

        assert_eq!(username_case_mapped(""), Err(PrecisError::EmptyInput));
        assert_eq!(
            username_case_mapped("user name"),
            Err(PrecisError::DisallowedCodePoint(0x0020))
        );
        assert_eq!(
            username_case_mapped("a\0b"),
            Err(PrecisError::DisallowedCodePoint(0x0000))
        );
        assert_eq!(
            username_case_mapped("u\ts"),
            Err(PrecisError::DisallowedCodePoint(0x0009))
        );
        assert_eq!(
            username_case_mapped("u\u{0085}s"),
            Err(PrecisError::DisallowedCodePoint(0x0085))
        );
        assert_eq!(
            username_case_mapped("u\u{E000}s"),
            Err(PrecisError::DisallowedCodePoint(0xE000))
        );
        assert_eq!(
            username_case_mapped("u\u{FDD0}s"),
            Err(PrecisError::DisallowedCodePoint(0xFDD0))
        );
        assert_eq!(
            username_case_mapped("u\u{FFFF}s"),
            Err(PrecisError::DisallowedCodePoint(0xFFFF))
        );
        assert_eq!(
            username_case_mapped("u\u{10FFFF}s"),
            Err(PrecisError::DisallowedCodePoint(0x10_FFFF))
        );

        // 大文字小文字不変性。
        assert_eq!(username_case_mapped("Alice"), username_case_mapped("ALICE"));
        assert_eq!(username_case_mapped("Alice"), username_case_mapped("alice"));
        assert_eq!(
            username_case_mapped("A\u{0308}"),
            username_case_mapped("a\u{0308}")
        );
    }

    #[test]
    fn test_all_allowed_and_find_disallowed_cp() {
        assert!(all_allowed(&[]));
        assert!(all_allowed(&[b'a' as u32, b'1' as u32, 0x3042]));
        assert_eq!(find_disallowed_cp(&[b'a' as u32, b'1' as u32]), None);
        assert_eq!(
            find_disallowed_cp(&[b'a' as u32, 0x20, 0x00]),
            Some(0x20),
            "先頭に現れる禁止コードポイントが返されることを確認。"
        );
        assert!(!all_allowed(&[b'a' as u32, 0xD800]));
    }

    #[test]
    fn test_compose_hangul_syllable_and_trailing() {
        // compose_hangul_syllable: 正常系(境界値および中間値)
        assert_eq!(compose_hangul_syllable(4352, 4449), Some(44032));
        assert_eq!(compose_hangul_syllable(4370, 4469), Some(55176));
        assert_eq!(compose_hangul_syllable(4352, 4450), Some(44060));

        // compose_hangul_syllable: 異常系(下限未満、上限超過、無効値)
        assert_eq!(compose_hangul_syllable(0, 0), None);
        assert_eq!(compose_hangul_syllable(4351, 4449), None);
        assert_eq!(compose_hangul_syllable(4371, 4449), None);
        assert_eq!(compose_hangul_syllable(4352, 4448), None);
        assert_eq!(compose_hangul_syllable(4352, 4470), None);
        assert_eq!(compose_hangul_syllable(u32::MAX, u32::MAX), None);

        // compose_hangul_trailing: 正常系(境界値および中間値)
        assert_eq!(compose_hangul_trailing(44032, 4520), Some(44033));
        assert_eq!(compose_hangul_trailing(55176, 4546), Some(55203));

        // compose_hangul_trailing: 異常系(非LV音節、終声範囲外、無効値)
        assert_eq!(compose_hangul_trailing(0, 0), None);
        assert_eq!(compose_hangul_trailing(44032, 4519), None);
        assert_eq!(compose_hangul_trailing(44032, 4547), None);
        // 44033 は既に終声を含むため LV 音節ではない。
        assert_eq!(compose_hangul_trailing(44033, 4520), None);
        // LV 音節の上限 55176 を超えるコードポイント。
        assert_eq!(compose_hangul_trailing(55177, 4520), None);
        assert_eq!(compose_hangul_trailing(u32::MAX, u32::MAX), None);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_precis_fold_string_and_nfc_helpers() {
        let folded = precis_fold_string(&[b'A' as u32, b'b' as u32, 0x0410]);
        assert_eq!(folded, alloc::vec![b'a' as u32, b'b' as u32, 0x0430]);
        assert_eq!(precis_fold_string(&folded), folded);

        // 非合成ペアの保持と連続合成の検証。
        assert_eq!(
            precis_nfc_normalize(&[b'a' as u32, b'b' as u32]),
            alloc::vec![b'a' as u32, b'b' as u32]
        );
        assert_eq!(
            precis_nfc_normalize(&[65, 776, 4352, 4449, 4520, b'z' as u32]),
            alloc::vec![196, 44033, b'z' as u32]
        );

        // Latin-1 残余合成ペア (Ñ/ñ, Ý/ý, ÿ) および大文字・小文字混在正規化の検証。
        assert_eq!(compose_pair(b'N' as u32, 0x0303), Some('Ñ' as u32));
        assert_eq!(compose_pair(b'n' as u32, 0x0303), Some('ñ' as u32));
        assert_eq!(compose_pair(b'Y' as u32, 0x0301), Some('Ý' as u32));
        assert_eq!(compose_pair(b'y' as u32, 0x0301), Some('ý' as u32));
        assert_eq!(compose_pair(b'y' as u32, 0x0308), Some('ÿ' as u32));
        assert_eq!(
            username_case_mapped("Español"),
            username_case_mapped("Espan\u{0303}ol")
        );
        assert_eq!(
            username_case_mapped("ESPAÑOL"),
            username_case_mapped("ESPAN\u{0303}OL")
        );
        assert_eq!(
            username_case_mapped("Ýýÿ"),
            username_case_mapped("Y\u{0301}y\u{0301}y\u{0308}")
        );
        assert_eq!(
            opaque_string("Español Ýýÿ"),
            opaque_string("Espan\u{0303}ol Y\u{0301}y\u{0301}y\u{0308}")
        );
    }

    #[test]
    fn test_opaque_disallowed_cp_boundaries() {
        // ASCII 空白 (0x20) は OpaqueString (FreeformClass) で許可される。
        assert!(!is_opaque_disallowed_cp(0x20));
        assert!(is_disallowed_cp(0x20));

        // 制御文字・サロゲート・私用領域・非文字・範囲外は禁止される。
        for &cp in &[
            0x00,
            0x09,
            0x0A,
            0x0D,
            0x1F,
            0x7F,
            0x80,
            0x85,
            0x9F,
            0xD800,
            0xDFFF,
            0xE000,
            0xF8FF,
            0xF_0000,
            0x10_FFFD,
            0xFDD0,
            0xFDEF,
            0xFFFE,
            0xFFFF,
            0x10_FFFF,
            0x11_0000,
            u32::MAX,
        ] {
            assert!(is_opaque_disallowed_cp(cp));
            assert!(is_disallowed_cp(cp));
        }

        // 一般文字 (ASCII大文字小文字、空白、日本語、絵文字等) は許可される。
        for &cp in &[b'A' as u32, b'z' as u32, 0x20, 0xA0, 0x3042, 0x1F511] {
            assert!(!is_opaque_disallowed_cp(cp));
        }
    }

    #[test]
    fn test_all_opaque_allowed_and_find_opaque_disallowed_cp() {
        assert!(all_opaque_allowed(&[]));
        assert!(all_opaque_allowed(&[
            b'P' as u32,
            0x20,
            b'w' as u32,
            0x3042
        ]));
        assert_eq!(
            find_opaque_disallowed_cp(&[b'P' as u32, 0x20, b'w' as u32]),
            None
        );
        assert_eq!(
            find_opaque_disallowed_cp(&[b'a' as u32, 0x20, 0x1F, 0x00]),
            Some(0x1F),
            "空白をスキップし、最初に現れる FreeformClass 禁止文字が返されることを確認。"
        );
        assert!(!all_opaque_allowed(&[b'a' as u32, 0x20, 0xD800]));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_precis_profile_v_opaque_golden_vectors() {
        // PrecisProfile.v の precis_golden_suite (tc_expected_opaque) と全件一致を検証。
        let cases: &[(&[u32], Option<&[u32]>)] = &[
            (&[85, 115, 101, 114], Some(&[85, 115, 101, 114])),
            (&[85, 83, 69, 82], Some(&[85, 83, 69, 82])),
            (&[117, 115, 101, 114], Some(&[117, 115, 101, 114])),
            (&[927, 931], Some(&[927, 931])),
            (&[1048, 1074, 1072, 1085], Some(&[1048, 1074, 1072, 1085])),
            (&[201], Some(&[201])),
            (
                &[117, 115, 101, 114, 32, 110, 97, 109, 101],
                Some(&[117, 115, 101, 114, 32, 110, 97, 109, 101]),
            ),
            (&[], None),
            (&[0], None),
            (&[9], None),
            (&[55296], None),
            (&[57344], None),
            (&[65535], None),
            (&[64976], None),
            (&[101, 769], Some(&[233])),
            (&[65, 776], Some(&[196])),
            (&[99, 807], Some(&[231])),
            (&[4352, 4449], Some(&[44032])),
            (&[4352, 4449, 4520], Some(&[44033])),
            (&[44032, 4520], Some(&[44033])),
        ];

        for &(input, expected) in cases {
            let actual = precis_opaque_string(input);
            assert_eq!(
                actual.as_deref(),
                expected,
                "PrecisProfile.v の OpaqueString ゴールデンベクタ {input:?} が一致することを検証。"
            );
        }

        // opaque_string_password_with_space ("pass word") 検証。
        assert_eq!(
            precis_opaque_string(&[112, 97, 115, 115, 32, 119, 111, 114, 100]).as_deref(),
            Some(&[112, 97, 115, 115, 32, 119, 111, 114, 100][..])
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_opaque_string_str_api() {
        // 大文字小文字と ASCII 空白 (0x20) の保持。
        assert_eq!(opaque_string("PassWord"), Ok(String::from("PassWord")));
        assert_eq!(opaque_string("USER"), Ok(String::from("USER")));
        assert_eq!(opaque_string("ΟΣ"), Ok(String::from("ΟΣ")));
        assert_eq!(opaque_string("Иван"), Ok(String::from("Иван")));
        assert_eq!(opaque_string("É"), Ok(String::from("É")));
        assert_eq!(opaque_string("pass word"), Ok(String::from("pass word")));
        assert_eq!(opaque_string("user name"), Ok(String::from("user name")));
        assert_eq!(
            opaque_string("  leading and trailing  "),
            Ok(String::from("  leading and trailing  "))
        );

        // Unicode NFC 正規化 (大文字保持のまま結合文字を合成)。
        assert_eq!(opaque_string("e\u{0301}"), Ok(String::from("é")));
        assert_eq!(opaque_string("A\u{0308}"), Ok(String::from("Ä")));
        assert_eq!(opaque_string("c\u{0327}"), Ok(String::from("ç")));
        assert_eq!(opaque_string("\u{1100}\u{1161}"), Ok(String::from("가")));
        assert_eq!(
            opaque_string("\u{1100}\u{1161}\u{11A8}"),
            Ok(String::from("각"))
        );
        assert_eq!(opaque_string("\u{AC00}\u{11A8}"), Ok(String::from("각")));

        // 空入力および禁止コードポイントの拒絶。
        assert_eq!(opaque_string(""), Err(PrecisError::EmptyInput));
        assert_eq!(
            opaque_string("p\0w"),
            Err(PrecisError::DisallowedCodePoint(0x0000))
        );
        assert_eq!(
            opaque_string("p\tw"),
            Err(PrecisError::DisallowedCodePoint(0x0009))
        );
        assert_eq!(
            opaque_string("p\nw"),
            Err(PrecisError::DisallowedCodePoint(0x000A))
        );
        assert_eq!(
            opaque_string("p\x1Fw"),
            Err(PrecisError::DisallowedCodePoint(0x001F))
        );
        assert_eq!(
            opaque_string("p\x7Fw"),
            Err(PrecisError::DisallowedCodePoint(0x007F))
        );
        assert_eq!(
            opaque_string("p\u{0085}w"),
            Err(PrecisError::DisallowedCodePoint(0x0085))
        );
        assert_eq!(
            opaque_string("p\u{E000}w"),
            Err(PrecisError::DisallowedCodePoint(0xE000))
        );
        assert_eq!(
            opaque_string("p\u{FDD0}w"),
            Err(PrecisError::DisallowedCodePoint(0xFDD0))
        );
        assert_eq!(
            opaque_string("p\u{FFFF}w"),
            Err(PrecisError::DisallowedCodePoint(0xFFFF))
        );
        assert_eq!(
            opaque_string("p\u{10FFFF}w"),
            Err(PrecisError::DisallowedCodePoint(0x10_FFFF))
        );

        // UsernameCaseMapped と OpaqueString のプロファイル境界差分。
        assert_ne!(username_case_mapped("USER"), opaque_string("USER"));
        assert_eq!(
            username_case_mapped("user name"),
            Err(PrecisError::DisallowedCodePoint(0x0020))
        );
        assert_eq!(opaque_string("user name"), Ok(String::from("user name")));
        assert_eq!(username_case_mapped("A\u{0308}"), Ok(String::from("ä")));
        assert_eq!(opaque_string("A\u{0308}"), Ok(String::from("Ä")));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_opaque_string_secret_api() {
        let sec = opaque_string_secret("Pass\u{00A0}Word\u{0020}A\u{0308}").unwrap();
        assert_eq!(sec.as_slice(), "Pass Word Ä".as_bytes());

        assert_eq!(
            opaque_string_secret("").unwrap_err(),
            PrecisError::EmptyInput
        );
        assert_eq!(
            opaque_string_secret("bad\0pw").unwrap_err(),
            PrecisError::DisallowedCodePoint(0x0000)
        );
    }

    #[test]
    fn test_zs_space_mapping() {
        // Unicode Zs (Space_Separator) 全 17 文字の判定を検証。
        let zs_cps = [
            0x0020, 0x00A0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005, 0x2006, 0x2007,
            0x2008, 0x2009, 0x200A, 0x202F, 0x205F, 0x3000,
        ];
        for &cp in &zs_cps {
            assert!(
                is_zs_space(cp),
                "U+{cp:04X} は Unicode Zs 空白として判定される必要があります。"
            );
            assert_eq!(
                map_zs_to_space(cp),
                0x0020,
                "U+{cp:04X} は ASCII 空白 (0x0020) へマッピングされる必要があります。"
            );
        }

        // 境界値および非 Zs 空白文字 (Cf 等) が Zs 判定されないことを検証。
        let non_zs_cps = [
            0x001F, 0x0021, 0x009F, 0x00A1, 0x167F, 0x1681, 0x1FFF,
            0x200B, // ZERO WIDTH SPACE (Cf)
            0x202E, 0x2030, 0x205E, 0x2060, // WORD JOINER (Cf)
            0x2FFF, 0x3001, 0xFEFF, // ZERO WIDTH NO-BREAK SPACE (Cf)
        ];
        for &cp in &non_zs_cps {
            assert!(
                !is_zs_space(cp),
                "U+{cp:04X} は Unicode Zs 空白ではありません。"
            );
            assert_eq!(
                map_zs_to_space(cp),
                cp,
                "非 Zs コードポイント U+{cp:04X} はマッピングで変更されてはなりません。"
            );
        }

        // OpaqueString における非 ASCII 空白の ASCII 空白 (0x20) への正規化検証 (RFC 8265 Section 4.2.2)。
        #[cfg(feature = "alloc")]
        {
            // ノーブレークスペース (U+00A0)。
            assert_eq!(
                opaque_string("pass\u{00A0}word"),
                Ok(String::from("pass word"))
            );
            // 全角スペース (U+3000)。
            assert_eq!(
                opaque_string("パスワード\u{3000}秘密"),
                Ok(String::from("パスワード 秘密"))
            );
            // 複数種 Zs スペースの混在。
            assert_eq!(
                opaque_string("a\u{1680}b\u{2000}c\u{200A}d\u{202F}e\u{205F}f"),
                Ok(String::from("a b c d e f"))
            );

            // RFC 8265 Section 4.2.2 参照ベクタ (rfc8265_sec4_2_non_ascii_space_nbsp)。
            let nbsp_input = [112, 97, 115, 115, 160, 119, 111, 114, 100];
            let expected_opaque = [112, 97, 115, 115, 32, 119, 111, 114, 100];
            assert_eq!(
                precis_opaque_string(&nbsp_input).as_deref(),
                Some(&expected_opaque[..])
            );
            assert_eq!(
                enforce_opaque_string_cps(&nbsp_input).unwrap(),
                expected_opaque
            );

            // 冪等性: マッピング結果への再適用が同一結果を返すことを検証。
            let normalized = opaque_string("pass\u{00A0}word\u{3000}secret").unwrap();
            assert_eq!(opaque_string(&normalized).unwrap(), normalized);
        }
    }

    #[test]
    fn test_precis_profile_dispatch() {
        let user_prof = PrecisProfile::UsernameCaseMapped;
        let opaque_prof = PrecisProfile::OpaqueString;

        // label
        assert_eq!(user_prof.label(), "UsernameCaseMapped");
        assert_eq!(opaque_prof.label(), "OpaqueString");

        // is_disallowed_cp
        assert!(user_prof.is_disallowed_cp(0x20));
        assert!(!opaque_prof.is_disallowed_cp(0x20));
        assert!(user_prof.is_disallowed_cp(0x00));
        assert!(opaque_prof.is_disallowed_cp(0x00));

        // all_allowed & find_disallowed_cp
        let with_space = [b'u' as u32, 0x20, b's' as u32];
        assert!(!user_prof.all_allowed(&with_space));
        assert!(opaque_prof.all_allowed(&with_space));
        assert_eq!(user_prof.find_disallowed_cp(&with_space), Some(0x20));
        assert_eq!(opaque_prof.find_disallowed_cp(&with_space), None);

        // enforce_cps & precis_cps & enforce_str (feature = "alloc")
        #[cfg(feature = "alloc")]
        {
            let input_cps = [85, 83, 69, 82]; // "USER"
            assert_eq!(
                user_prof.enforce_cps(&input_cps),
                enforce_username_case_mapped_cps(&input_cps)
            );
            assert_eq!(
                opaque_prof.enforce_cps(&input_cps),
                enforce_opaque_string_cps(&input_cps)
            );
            assert_eq!(
                user_prof.precis_cps(&input_cps),
                precis_username_case_mapped(&input_cps)
            );
            assert_eq!(
                opaque_prof.precis_cps(&input_cps),
                precis_opaque_string(&input_cps)
            );

            assert_eq!(user_prof.enforce_str("User"), username_case_mapped("User"));
            assert_eq!(opaque_prof.enforce_str("User"), opaque_string("User"));
            assert_eq!(
                user_prof.enforce_str("user name"),
                Err(PrecisError::DisallowedCodePoint(0x0020))
            );
            assert_eq!(
                opaque_prof.enforce_str("user name"),
                Ok(alloc::string::String::from("user name"))
            );

            assert_eq!(
                user_prof.enforce_str_secret("User").unwrap().as_slice(),
                b"user"
            );
            assert_eq!(
                opaque_prof.enforce_str_secret("User").unwrap().as_slice(),
                b"User"
            );
            assert_eq!(
                user_prof.enforce_str_secret("user name").unwrap_err(),
                PrecisError::DisallowedCodePoint(0x0020)
            );
            assert_eq!(
                opaque_prof
                    .enforce_str_secret("user name")
                    .unwrap()
                    .as_slice(),
                b"user name"
            );
        }
    }

    proptest! {
        #[test]
        fn prop_case_fold_idempotent_and_preserves_allowed(cp in 0u32..=0x12_0000u32) {
            let folded = precis_fold_cp(cp);
            prop_assert_eq!(precis_fold_cp(folded), folded);
            if !is_disallowed_cp(cp) {
                prop_assert!(!is_disallowed_cp(folded));
            }
        }

        #[test]
        fn prop_opaque_disallowed_implies_disallowed(cp in 0u32..=0x12_0000u32) {
            if is_opaque_disallowed_cp(cp) {
                prop_assert!(is_disallowed_cp(cp));
            }
            if cp == 0x20 {
                prop_assert!(!is_opaque_disallowed_cp(cp));
                prop_assert!(is_disallowed_cp(cp));
            }
        }

        #[cfg(feature = "alloc")]
        #[test]
        fn prop_username_case_mapped_invariants(cps in proptest::collection::vec(0u32..=0x12_0000u32, 0..64)) {
            if let Some(normalized) = precis_username_case_mapped(&cps) {
                prop_assert!(!normalized.is_empty());
                prop_assert!(normalized.len() <= cps.len());
                prop_assert!(all_allowed(&normalized));
                let re_normalized = precis_username_case_mapped(&normalized);
                prop_assert_eq!(re_normalized.as_deref(), Some(normalized.as_slice()));
            }
        }

        #[cfg(feature = "alloc")]
        #[test]
        fn prop_opaque_string_invariants(cps in proptest::collection::vec(0u32..=0x12_0000u32, 0..64)) {
            if let Some(normalized) = precis_opaque_string(&cps) {
                prop_assert!(!normalized.is_empty());
                prop_assert!(normalized.len() <= cps.len());
                prop_assert!(all_opaque_allowed(&normalized));
                let re_normalized = precis_opaque_string(&normalized);
                prop_assert_eq!(re_normalized.as_deref(), Some(normalized.as_slice()));
            }
        }

        #[cfg(feature = "alloc")]
        #[test]
        fn prop_username_case_mapped_str_idempotent(input in "\\PC{0,48}") {
            if let Ok(normalized) = username_case_mapped(&input) {
                prop_assert!(!normalized.is_empty());
                prop_assert_eq!(username_case_mapped(&normalized), Ok(normalized.clone()));
            }
        }

        #[cfg(feature = "alloc")]
        #[test]
        fn prop_opaque_string_str_idempotent(input in "\\PC{0,48}") {
            if let Ok(normalized) = opaque_string(&input) {
                prop_assert!(!normalized.is_empty());
                prop_assert_eq!(opaque_string(&normalized), Ok(normalized.clone()));
            }
        }
    }
}
