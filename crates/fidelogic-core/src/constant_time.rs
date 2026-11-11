//! # 定数時間演算モジュール
//!
//! タイミング攻撃を遮断するための定数時間等価判定および条件選択ヘルパーを提供する。
//! `subtle` クレートを活用し、CPU条件分岐命令や早期リターン(Short-Circuiting)を排除した
//! 安全な暗号比較・選択処理を確立する。

use subtle::{
    Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
};

/// 2つのバイトスライスが等価であるかを定数時間で判定する。
///
/// 認証タグ、トークン、ハッシュ値等の比較において、早期リターン(Short-Circuiting)による
/// サイドチャネル情報漏洩(タイミング攻撃)を防止する。
///
/// 入力スライスの長さが異なる場合であっても、即時に判定を返さず、
/// 長い方の長さに合わせた定数時間走査を実行してタイミング差分を平滑化する。
///
/// # 戻り値
/// 両スライスの長さおよび内容が完全に一致する場合に `Choice::from(1)`(真)を返し、
/// それ以外の場合は `Choice::from(0)`(偽)を返す。
///
/// # 計算量
/// `O(max(a.len(), b.len()))` の定数時間ループを実行し、内部条件分岐命令(`if` / `br_if`)を発生させない。
#[inline]
#[must_use]
pub fn ct_eq_bytes(a: &[u8], b: &[u8]) -> Choice {
    let len_a = a.len();
    let len_b = b.len();

    // 長さの定数時間等価判定
    let len_match = (len_a as u64).ct_eq(&(len_b as u64));

    // 早期リターンを排除するため、max(len_a, len_b) の走査長を定数時間で決定
    let a_gt_b = (len_a as u64).ct_gt(&(len_b as u64));
    let max_len = ct_select(a_gt_b, len_a as u64, len_b as u64) as usize;

    // 空スライスに対する境界外パニック防止用ダミー参照。
    static DUMMY: [u8; 1] = [0];
    #[inline]
    fn non_empty_buf(s: &[u8]) -> &[u8] {
        if s.is_empty() { &DUMMY[..] } else { s }
    }
    let buf_a = non_empty_buf(a);
    let buf_b = non_empty_buf(b);

    let mut diff = 0u8;

    for i in 0..max_len {
        let i_u64 = i as u64;
        let valid_a = i_u64.ct_lt(&(len_a as u64));
        let valid_b = i_u64.ct_lt(&(len_b as u64));

        // 境界外アクセスの防止: 有効範囲外ならダミーインデックス 0 を定数時間選択
        let idx_a = ct_select(valid_a, i_u64, 0u64) as usize;
        let idx_b = ct_select(valid_b, i_u64, 0u64) as usize;

        let byte_a = buf_a[idx_a];
        let byte_b = buf_b[idx_b];

        let both_valid = valid_a & valid_b;
        let byte_diff = byte_a ^ byte_b;

        // 両方有効な場合は差分値、いずれかが無効な場合は不一致ビット(1)を選択
        let step_diff = ct_select(both_valid, byte_diff, 1u8);
        diff |= step_diff;
    }

    let bytes_match = diff.ct_eq(&0u8);
    len_match & bytes_match
}

/// 2つのバイトスライスが等価であるかを定数時間で判定し、`bool` 値として返す。
///
/// [`ct_eq_bytes`] の結果を `bool` に変換した利便性ヘルパー。
#[inline]
#[must_use]
pub fn ct_eq_bytes_bool(a: &[u8], b: &[u8]) -> bool {
    ct_eq_bytes(a, b).into()
}

/// 32バイト固定長バイト列の等価性を定数時間で判定する。
///
/// 認証タグ(Poly1305、HMAC等)や256ビット暗号トークンの照合において、
/// ループ継続判定を含む条件分岐命令(`br_if`, `if`, `br_table`)を完全に排除し、
/// ストレートラインなビット演算によりタイミング攻撃耐性を確立する。
#[inline]
#[must_use]
pub fn ct_eq_32(a: &[u8; 32], b: &[u8; 32]) -> Choice {
    let mut diff = 0u8;
    diff |= a[0] ^ b[0];
    diff |= a[1] ^ b[1];
    diff |= a[2] ^ b[2];
    diff |= a[3] ^ b[3];
    diff |= a[4] ^ b[4];
    diff |= a[5] ^ b[5];
    diff |= a[6] ^ b[6];
    diff |= a[7] ^ b[7];
    diff |= a[8] ^ b[8];
    diff |= a[9] ^ b[9];
    diff |= a[10] ^ b[10];
    diff |= a[11] ^ b[11];
    diff |= a[12] ^ b[12];
    diff |= a[13] ^ b[13];
    diff |= a[14] ^ b[14];
    diff |= a[15] ^ b[15];
    diff |= a[16] ^ b[16];
    diff |= a[17] ^ b[17];
    diff |= a[18] ^ b[18];
    diff |= a[19] ^ b[19];
    diff |= a[20] ^ b[20];
    diff |= a[21] ^ b[21];
    diff |= a[22] ^ b[22];
    diff |= a[23] ^ b[23];
    diff |= a[24] ^ b[24];
    diff |= a[25] ^ b[25];
    diff |= a[26] ^ b[26];
    diff |= a[27] ^ b[27];
    diff |= a[28] ^ b[28];
    diff |= a[29] ^ b[29];
    diff |= a[30] ^ b[30];
    diff |= a[31] ^ b[31];
    diff.ct_eq(&0u8)
}

/// 条件 `condition` に応じて定数時間で値を選択するヘルパー。
///
/// `condition` が真(`Choice(1)`)の場合は `true_val` を、
/// 偽(`Choice(0)`)の場合は `false_val` を定数時間で返す。
///
/// # ゼロコスト抽象化とサイドチャネル耐性
/// 内部で [`subtle::ConditionallySelectable::conditional_select`] を呼び出し、
/// CPUの条件分岐命令を排除してサイドチャネル攻撃(タイミング・キャッシュ攻撃)を防御する。
#[inline]
#[must_use]
pub fn ct_select<T: ConditionallySelectable>(condition: Choice, true_val: T, false_val: T) -> T {
    T::conditional_select(&false_val, &true_val, condition)
}

/// 条件 `condition` に応じてスライスの内容を定数時間で宛先 `dst` にコピーする。
///
/// `condition` が真(`Choice(1)`)の場合は `true_src` を、
/// 偽(`Choice(0)`)の場合は `false_src` を `dst` に定数時間で書き込む。
///
/// # パニック条件
/// `dst`, `true_src`, `false_src` の長さが互いに異なる場合はパニックする。
#[inline]
pub fn ct_select_slice(condition: Choice, dst: &mut [u8], true_src: &[u8], false_src: &[u8]) {
    assert_eq!(
        dst.len(),
        true_src.len(),
        "dst and true_src length mismatch"
    );
    assert_eq!(
        dst.len(),
        false_src.len(),
        "dst and false_src length mismatch"
    );

    for (d, (t, f)) in dst.iter_mut().zip(true_src.iter().zip(false_src.iter())) {
        *d = u8::conditional_select(f, t, condition);
    }
}

/// 条件 `condition` に応じてスライス `src` の内容を宛先 `dst` に定数時間で条件付き代入する。
///
/// `condition` が真(`Choice(1)`)の場合は `src` の各バイトが `dst` に上書き代入され、
/// 偽(`Choice(0)`)の場合は `dst` の元の値がそのまま維持される。
///
/// # パニック条件
/// `dst` と `src` の長さが異なる場合はパニックする。
#[inline]
pub fn ct_assign_slice(condition: Choice, dst: &mut [u8], src: &[u8]) {
    assert_eq!(dst.len(), src.len(), "dst and src length mismatch");
    for (d, s) in dst.iter_mut().zip(src.iter()) {
        *d = u8::conditional_select(d, s, condition);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ct_eq_bytes_identical() {
        let a = [1u8, 2, 3, 4, 5];
        let b = [1u8, 2, 3, 4, 5];
        assert_eq!(ct_eq_bytes(&a, &b).unwrap_u8(), 1);
        assert!(ct_eq_bytes_bool(&a, &b));
    }

    #[test]
    fn test_ct_eq_bytes_empty() {
        let empty_a: &[u8] = &[];
        let empty_b: &[u8] = &[];
        assert_eq!(ct_eq_bytes(empty_a, empty_b).unwrap_u8(), 1);
        assert!(ct_eq_bytes_bool(empty_a, empty_b));
    }

    #[test]
    fn test_ct_eq_bytes_different_content_same_length() {
        let a = [1u8, 2, 3, 4, 5];
        let b = [1u8, 2, 3, 4, 6];
        assert_eq!(ct_eq_bytes(&a, &b).unwrap_u8(), 0);
        assert!(!ct_eq_bytes_bool(&a, &b));

        let c = [0u8, 2, 3, 4, 5];
        assert_eq!(ct_eq_bytes(&a, &c).unwrap_u8(), 0);
        assert!(!ct_eq_bytes_bool(&a, &c));
    }

    #[test]
    fn test_ct_eq_bytes_different_length() {
        let a = [1u8, 2, 3, 4, 5];
        let b = [1u8, 2, 3, 4];
        assert_eq!(ct_eq_bytes(&a, &b).unwrap_u8(), 0);
        assert!(!ct_eq_bytes_bool(&a, &b));

        let empty: &[u8] = &[];
        assert_eq!(ct_eq_bytes(&a, empty).unwrap_u8(), 0);
        assert_eq!(ct_eq_bytes(empty, &a).unwrap_u8(), 0);
        assert!(!ct_eq_bytes_bool(&a, empty));
        assert!(!ct_eq_bytes_bool(empty, &a));
    }

    #[test]
    fn test_ct_select_u32() {
        let val_true = 100u32;
        let val_false = 200u32;

        let res_t = ct_select(Choice::from(1), val_true, val_false);
        assert_eq!(res_t, 100);

        let res_f = ct_select(Choice::from(0), val_true, val_false);
        assert_eq!(res_f, 200);
    }

    #[test]
    fn test_ct_select_u8() {
        let res_t = ct_select(Choice::from(1), 0xAAu8, 0xBBu8);
        assert_eq!(res_t, 0xAA);

        let res_f = ct_select(Choice::from(0), 0xAAu8, 0xBBu8);
        assert_eq!(res_f, 0xBB);
    }

    #[test]
    fn test_ct_select_slice() {
        let true_src = [10u8, 20, 30, 40];
        let false_src = [50u8, 60, 70, 80];

        let mut dst = [0u8; 4];
        ct_select_slice(Choice::from(1), &mut dst, &true_src, &false_src);
        assert_eq!(dst, true_src);

        ct_select_slice(Choice::from(0), &mut dst, &true_src, &false_src);
        assert_eq!(dst, false_src);
    }

    #[test]
    #[should_panic(expected = "dst and true_src length mismatch")]
    fn test_ct_select_slice_len_mismatch() {
        let true_src = [10u8, 20];
        let false_src = [50u8, 60, 70];
        let mut dst = [0u8; 3];
        ct_select_slice(Choice::from(1), &mut dst, &true_src, &false_src);
    }

    #[test]
    fn test_ct_assign_slice() {
        let mut dst = [1u8, 2, 3, 4];
        let src = [10u8, 20, 30, 40];

        // 偽の場合は変更されない
        ct_assign_slice(Choice::from(0), &mut dst, &src);
        assert_eq!(dst, [1u8, 2, 3, 4]);

        // 真の場合は上書き代入される
        ct_assign_slice(Choice::from(1), &mut dst, &src);
        assert_eq!(dst, [10u8, 20, 30, 40]);
    }

    #[test]
    #[should_panic(expected = "dst and src length mismatch")]
    fn test_ct_assign_slice_len_mismatch() {
        let mut dst = [1u8, 2];
        let src = [10u8, 20, 30];
        ct_assign_slice(Choice::from(1), &mut dst, &src);
    }

    #[test]
    fn test_secret_bytes_ct_eq() {
        use crate::zeroize::SecretBytes;

        let a = SecretBytes::new([1u8, 2, 3, 4]);
        let b = SecretBytes::new([1u8, 2, 3, 4]);
        let c = SecretBytes::new([1u8, 2, 3, 5]);

        assert_eq!(a.ct_eq(&b).unwrap_u8(), 1);
        assert_eq!(a.ct_eq(&c).unwrap_u8(), 0);
    }

    #[test]
    fn test_secret_bytes_conditional_assign() {
        use crate::zeroize::SecretBytes;

        let mut a = SecretBytes::new([1u8, 2, 3, 4]);
        let b = SecretBytes::new([10u8, 20, 30, 40]);

        // Choice(0): 値は維持される
        a.conditional_assign(&b, Choice::from(0));
        assert_eq!(a.as_bytes(), &[1u8, 2, 3, 4]);

        // Choice(1): b の値で上書きされる
        a.conditional_assign(&b, Choice::from(1));
        assert_eq!(a.as_bytes(), &[10u8, 20, 30, 40]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_secret_vec_ct_eq() {
        use crate::zeroize::SecretVec;

        let a = SecretVec::from_slice(&[1u8, 2, 3, 4]);
        let b = SecretVec::from_slice(&[1u8, 2, 3, 4]);
        let c = SecretVec::from_slice(&[1u8, 2, 3, 5]);
        let d = SecretVec::from_slice(&[1u8, 2, 3]);

        assert_eq!(a.ct_eq(&b).unwrap_u8(), 1);
        assert_eq!(a.ct_eq(&c).unwrap_u8(), 0);
        assert_eq!(a.ct_eq(&d).unwrap_u8(), 0);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_ct_eq_bytes_proptest() {
        use proptest::prelude::*;

        proptest!(|(a: alloc::vec::Vec<u8>, b: alloc::vec::Vec<u8>)| {
            let expected = a == b;
            let ct_result = ct_eq_bytes_bool(&a, &b);
            prop_assert_eq!(ct_result, expected);
        });
    }

    #[test]
    fn test_ct_eq_32() {
        let a = [0x5Au8; 32];
        let b = [0x5Au8; 32];
        let mut c = [0x5Au8; 32];
        c[31] = 0x5B;

        assert_eq!(ct_eq_32(&a, &b).unwrap_u8(), 1);
        assert_eq!(ct_eq_32(&a, &c).unwrap_u8(), 0);
    }
}
