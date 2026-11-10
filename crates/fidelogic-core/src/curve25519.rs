//! # 楕円曲線暗号モジュール(Curve25519 / Ristretto255)
//!
//! `curve25519-dalek` クレートを用いた、フットプリント最小化楕円曲線演算エンジンを提供する。
//! `precomputed-tables` フィーチャーを明示的に除外(`default-features = false`)し、
//! 約400KBの静的ルックアップテーブルをデータセクションから完全に排除した構成をとる。
//! これにより、ベースポイント乗算は可変ベースポイント乗算アルゴリズムへ動的にフォールバックし、
//! 極小のバイナリフットプリントを維持しつつ安全な楕円曲線演算を実現する。

pub use curve25519_dalek::constants::{ED25519_BASEPOINT_POINT, RISTRETTO_BASEPOINT_POINT};
pub use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
pub use curve25519_dalek::montgomery::MontgomeryPoint;
pub use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
pub use curve25519_dalek::scalar::Scalar;
use zeroize::Zeroize;

use crate::constant_time::ct_eq_32;
use crate::error::CryptoError;
use crate::zeroize::SecretBytes;

/// Ed25519ベースポイントに対する可変ベースポイントスカラー倍算を実行する。
///
/// 事前計算テーブルを除外した構成において、動的スカラー倍算(`ED25519_BASEPOINT_POINT * scalar`)にフォールバックする。
#[inline]
#[must_use]
pub fn edwards_basepoint_mul(scalar: &Scalar) -> EdwardsPoint {
    EdwardsPoint::mul_base(scalar)
}

/// Ristretto255ベースポイントに対する可変ベースポイントスカラー倍算を実行する。
///
/// 事前計算テーブルを除外した構成において、動的スカラー倍算(`RISTRETTO_BASEPOINT_POINT * scalar`)にフォールバックする。
#[inline]
#[must_use]
pub fn ristretto_basepoint_mul(scalar: &Scalar) -> RistrettoPoint {
    RistrettoPoint::mul_base(scalar)
}

/// RFC 7748 X25519 ベースポイントスカラー倍算を実行する。
///
/// クランプ処理を内部で行い、可変ベースポイントフォールバックにより計算された公開鍵(u座標32バイト)を返す。
#[inline]
#[must_use]
pub fn x25519_basepoint_mul(secret_key: &[u8; 32]) -> [u8; 32] {
    let point = MontgomeryPoint::mul_base_clamped(*secret_key);
    point.to_bytes()
}

/// RFC 7748 X25519 Diffie-Hellman 鍵共有演算を実行する。
///
/// 秘密鍵とピアの公開鍵からクランプ乗算を行い、共有秘密(u座標32バイト)を導出する。
/// RFC 7748 Section 6.1 の規定に基づき、低位数点攻撃を防御するため、
/// 導出された共有秘密が全ゼロ(All-zero output)であるかを定数時間で検証する。
/// 全ゼロが検出された場合は処理を中断し、[`CryptoError::InvalidParameter`] を返却する。
/// 正常に導出された共有秘密は、メモリ自動ゼロ消去が保証された [`SecretBytes<32>`] でラップして返却する。
///
/// # エラー
/// ピアの公開鍵が低位数点(位数 1, 2, 4, 8)等であり、計算された共有秘密が全ゼロとなる場合に
/// [`CryptoError::InvalidParameter`] を返す。
#[inline]
pub fn x25519_diffie_hellman(
    secret_key: &[u8; 32],
    public_key: &[u8; 32],
) -> Result<SecretBytes<32>, CryptoError> {
    let peer_point = MontgomeryPoint(*public_key);
    let shared = peer_point.mul_clamped(*secret_key);
    let mut bytes = shared.to_bytes();

    let is_all_zero: bool = ct_eq_32(&bytes, &[0u8; 32]).into();
    if is_all_zero {
        bytes.zeroize();
        return Err(CryptoError::InvalidParameter);
    }

    Ok(SecretBytes::new(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_edwards_basepoint_mul_variable_fallback() {
        let scalar_one = Scalar::ONE;
        let point = edwards_basepoint_mul(&scalar_one);
        assert_eq!(
            point, ED25519_BASEPOINT_POINT,
            "Ed25519ベースポイントの1倍算検証に成功。"
        );

        let scalar_two = Scalar::from(2u64);
        let point_two = edwards_basepoint_mul(&scalar_two);
        let point_add = ED25519_BASEPOINT_POINT + ED25519_BASEPOINT_POINT;
        assert_eq!(
            point_two, point_add,
            "Ed25519可変ベースポイント乗算と加算の整合性検証に成功。"
        );
    }

    #[test]
    fn test_ristretto_basepoint_mul_variable_fallback() {
        let scalar_one = Scalar::ONE;
        let point = ristretto_basepoint_mul(&scalar_one);
        assert_eq!(
            point, RISTRETTO_BASEPOINT_POINT,
            "Ristretto255ベースポイントの1倍算検証に成功。"
        );

        let s1 = Scalar::from(42u64);
        let s2 = Scalar::from(58u64);
        let p1 = ristretto_basepoint_mul(&s1);
        let p2 = ristretto_basepoint_mul(&s2);
        let p_sum = ristretto_basepoint_mul(&(s1 + s2));
        assert_eq!(
            p1 + p2,
            p_sum,
            "Ristretto255可変ベースポイント準同型加算検証に成功。"
        );
    }

    #[test]
    fn test_x25519_rfc7748_test_vectors() {
        // RFC 7748 Section 6.1 テストベクタ
        let alice_private = [
            0x77, 0x07, 0x6d, 0x0a, 0x73, 0x18, 0xa5, 0x7d, 0x3c, 0x16, 0xc1, 0x72, 0x51, 0xb2,
            0x66, 0x45, 0xdf, 0x4c, 0x2f, 0x87, 0xeb, 0xc0, 0x99, 0x2a, 0xb1, 0x77, 0xfb, 0xa5,
            0x1d, 0xb9, 0x2c, 0x2a,
        ];
        // Alice expected public key:
        // 85 20 f0 09 89 30 a7 54 74 8b 7d dc b4 3e f7 5a 0d bf 3a 0d 26 38 1a f4 eb a4 a9 8e aa 9b 4e 6a
        let alice_expected_public = [
            0x85, 0x20, 0xf0, 0x09, 0x89, 0x30, 0xa7, 0x54, 0x74, 0x8b, 0x7d, 0xdc, 0xb4, 0x3e,
            0xf7, 0x5a, 0x0d, 0xbf, 0x3a, 0x0d, 0x26, 0x38, 0x1a, 0xf4, 0xeb, 0xa4, 0xa9, 0x8e,
            0xaa, 0x9b, 0x4e, 0x6a,
        ];
        let alice_public_calc = x25519_basepoint_mul(&alice_private);
        assert_eq!(
            alice_public_calc, alice_expected_public,
            "Alice公開鍵のRFC 7748テストベクタ一致検証に成功。"
        );

        // Bob private key (RFC 7748: 5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb)
        let bob_private = [
            0x5d, 0xab, 0x08, 0x7e, 0x62, 0x4a, 0x8a, 0x4b, 0x79, 0xe1, 0x7f, 0x8b, 0x83, 0x80,
            0x0e, 0xe6, 0x6f, 0x3b, 0xb1, 0x29, 0x26, 0x18, 0xb6, 0xfd, 0x1c, 0x2f, 0x8b, 0x27,
            0xff, 0x88, 0xe0, 0xeb,
        ];
        let bob_expected_public = [
            0xde, 0x9e, 0xdb, 0x7d, 0x7b, 0x7d, 0xc1, 0xb4, 0xd3, 0x5b, 0x61, 0xc2, 0xec, 0xe4,
            0x35, 0x37, 0x3f, 0x83, 0x43, 0xc8, 0x5b, 0x78, 0x67, 0x4d, 0xad, 0xfc, 0x7e, 0x14,
            0x6f, 0x88, 0x2b, 0x4f,
        ];
        let bob_public_calc = x25519_basepoint_mul(&bob_private);
        assert_eq!(
            bob_public_calc, bob_expected_public,
            "Bob公開鍵のRFC 7748テストベクタ一致検証に成功。"
        );

        // DH shared secret
        let shared_alice = x25519_diffie_hellman(&alice_private, &bob_public_calc)
            .expect("Aliceの共有秘密計算に成功。");
        let shared_bob = x25519_diffie_hellman(&bob_private, &alice_public_calc)
            .expect("Bobの共有秘密計算に成功。");
        assert_eq!(
            shared_alice.as_bytes(),
            shared_bob.as_bytes(),
            "X25519 Diffie-Hellman共有秘密の一致検証に成功。"
        );

        // RFC 7748 Section 6.1 の共有秘密 K:
        // 4a 5d 9d 5b a4 ce 2d e1 72 8e 3b f4 80 35 0f 25 e0 7e 21 c9 47 d1 9e 33 76 f0 9b 3c 1e 16 17 42
        let expected_shared = [
            0x4a, 0x5d, 0x9d, 0x5b, 0xa4, 0xce, 0x2d, 0xe1, 0x72, 0x8e, 0x3b, 0xf4, 0x80, 0x35,
            0x0f, 0x25, 0xe0, 0x7e, 0x21, 0xc9, 0x47, 0xd1, 0x9e, 0x33, 0x76, 0xf0, 0x9b, 0x3c,
            0x1e, 0x16, 0x17, 0x42,
        ];
        assert_eq!(
            shared_alice.as_bytes(),
            &expected_shared,
            "RFC 7748 X25519テストベクタ共有秘密との一致検証に成功。"
        );
    }

    #[test]
    fn test_x25519_small_subgroup_all_zero_rejection() {
        let private_key = [0x42u8; 32];

        // 1. 全ゼロ公開鍵 (低位数点 u = 0)
        let zero_public = [0u8; 32];
        let res_zero = x25519_diffie_hellman(&private_key, &zero_public);
        assert_eq!(
            res_zero.unwrap_err(),
            CryptoError::InvalidParameter,
            "全ゼロ公開鍵に対するDH共有秘密遮断に成功。"
        );

        // 2. 低位数点 u = 1 ([1, 0, 0, ..., 0])
        let mut u_one_public = [0u8; 32];
        u_one_public[0] = 1;
        let res_u_one = x25519_diffie_hellman(&private_key, &u_one_public);
        assert_eq!(
            res_u_one.unwrap_err(),
            CryptoError::InvalidParameter,
            "低位数点(u=1)公開鍵に対するDH共有秘密遮断に成功。"
        );
    }

    #[test]
    fn test_scalar_zeroize_and_constant_time_eq() {
        use subtle::ConstantTimeEq;
        use zeroize::Zeroize;

        let mut s = Scalar::from(123456789u64);
        assert!(!bool::from(s.ct_eq(&Scalar::ZERO)));

        s.zeroize();
        assert!(
            bool::from(s.ct_eq(&Scalar::ZERO)),
            "Scalarのzeroizeによる完全ゼロ消去検証に成功。"
        );
    }
}
