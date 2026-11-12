//! # PRECIS プロファイル正準化エンジン (RFC 7564 / RFC 8265)。
//!
//! 形式仕様 `proofs/Theories/PrecisProfile.v` に対応し、
//! 禁止コードポイント判定、純粋関数型 Case Folding、正準合成 (NFC)、
//! `UsernameCaseMapped` および `OpaqueString` プロファイル正準化を提供する。

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};

#[cfg(feature = "alloc")]
use crate::error::PrecisError;

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
    find_disallowed_cp(cps).is_none()
}

/// コードポイント列を先頭から走査し、最初に検出された禁止コードポイントを返す。
#[inline]
#[must_use]
pub fn find_disallowed_cp(cps: &[u32]) -> Option<u32> {
    cps.iter().copied().find(|&cp| is_disallowed_cp(cp))
}

/// コードポイント列のすべての要素が `FreeformClass` (`OpaqueString`) で許可されているかを判定する。
#[inline]
#[must_use]
pub fn all_opaque_allowed(cps: &[u32]) -> bool {
    find_opaque_disallowed_cp(cps).is_none()
}

/// コードポイント列を先頭から走査し、`FreeformClass` で最初に検出された禁止コードポイントを返す。
#[inline]
#[must_use]
pub fn find_opaque_disallowed_cp(cps: &[u32]) -> Option<u32> {
    cps.iter().copied().find(|&cp| is_opaque_disallowed_cp(cp))
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
    if in_range(65, 90, cp)
        || in_range(192, 214, cp)
        || in_range(216, 222, cp)
        || in_range(913, 929, cp)
        || in_range(931, 939, cp)
        || in_range(1040, 1071, cp)
    {
        cp + 32
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
    cps.iter().copied().map(precis_fold_cp).collect()
}

/// ハングル音節合成 (`Jamo L + V -> LV`) を計算する。
#[inline]
#[must_use]
pub const fn compose_hangul_syllable(l: u32, v: u32) -> u32 {
    let l_idx = l.saturating_sub(HANGUL_L_BASE);
    let v_idx = v.saturating_sub(HANGUL_V_BASE);
    HANGUL_S_BASE
        .saturating_add(l_idx.saturating_mul(HANGUL_N_COUNT))
        .saturating_add(v_idx.saturating_mul(HANGUL_T_COUNT))
}

/// ハングル音節終声合成 (`LV + T -> LVT`) を計算する。
#[inline]
#[must_use]
pub const fn compose_hangul_trailing(lv: u32, t: u32) -> u32 {
    lv.saturating_add(t.saturating_sub(HANGUL_T_BASE))
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
        // Latin 'A' (65) / 'a' (97)。
        (65, 768) => Some(192),
        (65, 769) => Some(193),
        (65, 770) => Some(194),
        (65, 771) => Some(195),
        (65, 776) => Some(196),
        (65, 778) => Some(197),
        (97, 768) => Some(224),
        (97, 769) => Some(225),
        (97, 770) => Some(226),
        (97, 771) => Some(227),
        (97, 776) => Some(228),
        (97, 778) => Some(229),
        // Latin 'C' (67) / 'c' (99)。
        (67, 807) => Some(199),
        (99, 807) => Some(231),
        // Latin 'E' (69) / 'e' (101)。
        (69, 768) => Some(200),
        (69, 769) => Some(201),
        (69, 770) => Some(202),
        (69, 776) => Some(203),
        (101, 768) => Some(232),
        (101, 769) => Some(233),
        (101, 770) => Some(234),
        (101, 776) => Some(235),
        // Latin 'I' (73) / 'i' (105)。
        (73, 768) => Some(204),
        (73, 769) => Some(205),
        (73, 770) => Some(206),
        (73, 776) => Some(207),
        (105, 768) => Some(236),
        (105, 769) => Some(237),
        (105, 770) => Some(238),
        (105, 776) => Some(239),
        // Latin 'N' (78) / 'n' (110)。
        (78, 771) => Some(209),
        (110, 771) => Some(241),
        // Latin 'O' (79) / 'o' (111)。
        (79, 768) => Some(210),
        (79, 769) => Some(211),
        (79, 770) => Some(212),
        (79, 771) => Some(213),
        (79, 776) => Some(214),
        (111, 768) => Some(242),
        (111, 769) => Some(243),
        (111, 770) => Some(244),
        (111, 771) => Some(245),
        (111, 776) => Some(246),
        // Latin 'U' (85) / 'u' (117)。
        (85, 768) => Some(217),
        (85, 769) => Some(218),
        (85, 770) => Some(219),
        (85, 776) => Some(220),
        (117, 768) => Some(249),
        (117, 769) => Some(250),
        (117, 770) => Some(251),
        (117, 776) => Some(252),
        // Latin 'Y' (89) / 'y' (121)。
        (89, 769) => Some(221),
        (121, 769) => Some(253),
        (121, 776) => Some(255),
        // ハングル L + V および LV + T。
        _ if in_range(HANGUL_L_BASE, HANGUL_L_END, c1)
            && in_range(HANGUL_V_BASE, HANGUL_V_END, c2) =>
        {
            Some(compose_hangul_syllable(c1, c2))
        }
        _ if in_range(HANGUL_S_BASE, HANGUL_LV_END, c1)
            && (c1 - HANGUL_S_BASE).is_multiple_of(HANGUL_T_COUNT)
            && in_range(HANGUL_T_START, HANGUL_T_END, c2) =>
        {
            Some(compose_hangul_trailing(c1, c2))
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
    let mut out = Vec::with_capacity(cps.len());
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

    out
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

    let folded = precis_fold_string(cps);
    let normalized = precis_nfc_normalize(&folded);
    if let Some(disallowed) = find_disallowed_cp(&normalized) {
        return Err(PrecisError::DisallowedCodePoint(disallowed));
    }

    Ok(normalized)
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

    let cps: Vec<u32> = input.chars().map(|ch| ch as u32).collect();
    let normalized = enforce_cps(&cps)?;

    let mut out = String::with_capacity(input.len());
    for cp in normalized {
        let ch = char::from_u32(cp).ok_or(PrecisError::DisallowedCodePoint(cp))?;
        out.push(ch);
    }

    Ok(out)
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

/// コードポイント列に対して `OpaqueString` プロファイル正準化 (RFC 8265 Section 4.2 形式モデル) を適用する。
///
/// `proofs/Theories/PrecisProfile.v` の仕様に一致する範囲を実装する
/// (RFC 8265 Section 4.2.2 の非 ASCII 空白 `Zs` -> `U+0020` マッピングおよび全 Unicode NFC テーブルは含まない)。
///
/// 処理手順を以下に示す。
/// 1. 空入力を拒絶 ([`PrecisError::EmptyInput`])。
/// 2. Case Folding を行わずに Unicode NFC 正規化 (`precis_nfc_normalize`) を適用。
/// 3. `FreeformClass` 禁止コードポイント検査 (`find_opaque_disallowed_cp`) を実施し、
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

    let normalized = precis_nfc_normalize(cps);
    if let Some(disallowed) = find_opaque_disallowed_cp(&normalized) {
        return Err(PrecisError::DisallowedCodePoint(disallowed));
    }

    Ok(normalized)
}

/// `PrecisProfile.v` (`precis_opaque_string`) に対応する `Option` 返却ラッパー。
#[cfg(feature = "alloc")]
#[must_use]
pub fn precis_opaque_string(cps: &[u32]) -> Option<Vec<u32>> {
    enforce_opaque_string_cps(cps).ok()
}

/// UTF-8 文字列に対して `OpaqueString` プロファイル正準化 (RFC 8265 Section 4.2) を適用する。
///
/// 大文字・小文字の区別と ASCII 空白 (`0x20`) を保持したまま Unicode NFC 正規化を適用し、
/// 制御文字・サロゲート・私用領域・非文字等の禁止コードポイントを拒絶する。
///
/// # Errors
///
/// 入力が空文字列であるか、正規化後に `FreeformClass` の禁止コードポイントが含まれる場合は [`PrecisError`] を返す。
#[cfg(feature = "alloc")]
pub fn opaque_string(input: &str) -> Result<String, PrecisError> {
    apply_str_profile(input, enforce_opaque_string_cps)
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
