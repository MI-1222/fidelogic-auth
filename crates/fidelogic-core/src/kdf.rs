//! # 鍵導出モジュール (KDF: Key Derivation Function)
//!
//! Argon2id (RFC 9106) に基づくパスワード鍵導出機能、
//! および HKDF-SHA256 (RFC 5869) に基づく鍵展開機能を提供する。
//! Native環境におけるマルチコア並列化 (`parallel` フィーチャーおよびレーン並列度) と、
//! WebAssembly (Wasm) やエッジ環境におけるシングルスレッド実行の差異を吸収する、
//! パラメータ抽象化構造体 [`Argon2Params`] を定義する。

use argon2::{Algorithm, Argon2, Params, Version};
use hkdf::Hkdf;
use sha2::Sha256;

use crate::error::CryptoError;
use crate::zeroize::{SecretBytes, volatile_zeroize};

#[cfg(feature = "alloc")]
use crate::zeroize::SecretVec;

/// SHA-256 ダイジェストおよび HKDF-SHA256 PRK の標準長 (32バイト)。
pub const HKDF_SHA256_HASH_LEN: usize = 32;

/// RFC 5869 規定における HKDF-SHA256 の最大出力長 (`255 * HashLen` = 8160バイト)。
pub const HKDF_SHA256_MAX_OUTPUT_LEN: usize = 255 * HKDF_SHA256_HASH_LEN;

/// Native環境における既定のメモリコスト(KiB単位: 64 MiB)
pub const DEFAULT_NATIVE_M_COST: u32 = 65536;

/// Native環境における既定の時間コスト(反復回数)
pub const DEFAULT_NATIVE_T_COST: u32 = 3;

/// Native環境における既定の並列度(レーン数)
pub const DEFAULT_NATIVE_P_COST: u32 = 4;

/// Wasmおよびシングルスレッド環境における既定のメモリコスト(KiB単位: 19 MiB)
pub const DEFAULT_WASM_M_COST: u32 = 19456;

/// Wasmおよびシングルスレッド環境における既定の時間コスト(反復回数)
pub const DEFAULT_WASM_T_COST: u32 = 2;

/// Wasmおよびシングルスレッド環境における既定の並列度(シングルスレッド固定)
pub const DEFAULT_WASM_P_COST: u32 = 1;

/// 高速テスト用の極小メモリコスト(KiB単位: 64 KiB)
pub const FAST_TEST_M_COST: u32 = 64;

/// 高速テスト用の極小時問コスト。
pub const FAST_TEST_T_COST: u32 = 1;

/// 高速テスト用の極小並列度。
pub const FAST_TEST_P_COST: u32 = 1;

/// 既定の導出鍵長(32バイト = 256ビット)
pub const DEFAULT_KEY_LEN: usize = 32;

/// Argon2id 鍵導出パラメータ抽象化構造体。
///
/// Native環境でのマルチスレッド並列実行と、Wasm環境でのシングルスレッド制約を
/// 透過的に切り替え可能にし、RFC 9106 準拠の鍵導出を安全に実行する。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Argon2Params {
    /// メモリコスト(KiB単位)RFC 9106規定により最低 `8 * p_cost` KiB 必要。
    m_cost: u32,
    /// 時間コスト(反復回数)1以上である必要がある。
    t_cost: u32,
    /// 並列度(スレッド/レーン数)1以上である必要がある。
    p_cost: u32,
    /// 導出される鍵のバイト長。
    output_len: usize,
    /// Argon2アルゴリズムの種類。
    algorithm: Algorithm,
    /// Argon2バージョン。
    version: Version,
}

impl Default for Argon2Params {
    /// ターゲット環境およびフィーチャー設定に応じた既定パラメータを返す。
    ///
    /// - `wasm32` ターゲット: シングルスレッド実行用の [`Argon2Params::for_wasm`] を自動選択。
    /// - 非 `wasm32` ターゲットかつ `parallel` フィーチャー有効: マルチコア並列化用の [`Argon2Params::for_native`] を自動選択。
    /// - 非 `wasm32` ターゲットかつ `parallel` フィーチャー無効: シングルスレッド用の [`Argon2Params::for_wasm`] を安全に選択。
    fn default() -> Self {
        #[cfg(target_arch = "wasm32")]
        {
            Self::for_wasm()
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            #[cfg(feature = "parallel")]
            {
                Self::for_native()
            }
            #[cfg(not(feature = "parallel"))]
            {
                Self::for_wasm()
            }
        }
    }
}

impl Argon2Params {
    /// Native環境向けの推奨マルチコア並列化パラメータを構築する。
    ///
    /// メモリコスト 64 MiB(65536 KiB)、反復回数 3、並列度 4、鍵長 32 バイト(Argon2id v0x13)
    #[must_use]
    pub const fn for_native() -> Self {
        Self {
            m_cost: DEFAULT_NATIVE_M_COST,
            t_cost: DEFAULT_NATIVE_T_COST,
            p_cost: DEFAULT_NATIVE_P_COST,
            output_len: DEFAULT_KEY_LEN,
            algorithm: Algorithm::Argon2id,
            version: Version::V0x13,
        }
    }

    /// Wasmおよびシングルスレッド環境向けの推奨パラメータを構築する。
    ///
    /// メモリコスト 19 MiB(19456 KiB)、反復回数 2、並列度 1、鍵長 32 バイト(Argon2id v0x13)
    #[must_use]
    pub const fn for_wasm() -> Self {
        Self {
            m_cost: DEFAULT_WASM_M_COST,
            t_cost: DEFAULT_WASM_T_COST,
            p_cost: DEFAULT_WASM_P_COST,
            output_len: DEFAULT_KEY_LEN,
            algorithm: Algorithm::Argon2id,
            version: Version::V0x13,
        }
    }

    /// テストおよび高速検証向けの極小パラメータを構築する。
    ///
    /// メモリコスト 64 KiB、反復回数 1、並列度 1、鍵長 32 バイト。
    #[must_use]
    pub const fn fast_test() -> Self {
        Self {
            m_cost: FAST_TEST_M_COST,
            t_cost: FAST_TEST_T_COST,
            p_cost: FAST_TEST_P_COST,
            output_len: DEFAULT_KEY_LEN,
            algorithm: Algorithm::Argon2id,
            version: Version::V0x13,
        }
    }

    /// メモリコスト(KiB単位)を上書きした新しいパラメータを返す。
    ///
    /// 値の妥当性は [`Self::validate`] または [`Self::validated`] で検証すること。
    #[must_use]
    pub const fn with_m_cost(mut self, m_cost: u32) -> Self {
        self.m_cost = m_cost;
        self
    }

    /// 時間コスト(反復回数)を上書きした新しいパラメータを返す。
    ///
    /// 値の妥当性は [`Self::validate`] または [`Self::validated`] で検証すること。
    #[must_use]
    pub const fn with_t_cost(mut self, t_cost: u32) -> Self {
        self.t_cost = t_cost;
        self
    }

    /// 並列度(スレッド/レーン数)を上書きした新しいパラメータを返す。
    ///
    /// 値の妥当性は [`Self::validate`] または [`Self::validated`] で検証すること。
    #[must_use]
    pub const fn with_p_cost(mut self, p_cost: u32) -> Self {
        self.p_cost = p_cost;
        self
    }

    /// 導出鍵長(バイト単位)を上書きした新しいパラメータを返す。
    ///
    /// 値の妥当性は [`Self::validate`] または [`Self::validated`] で検証すること。
    #[must_use]
    pub const fn with_output_len(mut self, output_len: usize) -> Self {
        self.output_len = output_len;
        self
    }

    /// パラメータを検証し、妥当であれば自身を返す。
    ///
    /// # エラー
    ///
    /// パラメータが RFC 9106 または `argon2` クレートの制約を満たさない場合に
    /// [`CryptoError::InvalidParameter`] を返す。
    pub fn validated(self) -> Result<Self, CryptoError> {
        self.validate()?;
        Ok(self)
    }

    /// カスタムパラメータを指定して検証済みの構造体を生成する。
    ///
    /// # エラー
    ///
    /// パラメータが RFC 9106 または argon2 クレートの制約を満たさない場合に
    /// [`CryptoError::InvalidParameter`] を返す。
    pub fn custom(
        m_cost: u32,
        t_cost: u32,
        p_cost: u32,
        output_len: Option<usize>,
    ) -> Result<Self, CryptoError> {
        let out_len = output_len.unwrap_or(DEFAULT_KEY_LEN);

        Self::for_wasm()
            .with_m_cost(m_cost)
            .with_t_cost(t_cost)
            .with_p_cost(p_cost)
            .with_output_len(out_len)
            .validated()
    }

    /// パラメータが有効範囲内にあるかを検証する。
    pub fn validate(&self) -> Result<(), CryptoError> {
        if self.t_cost == 0 || self.p_cost == 0 {
            return Err(CryptoError::InvalidParameter);
        }

        // RFC 9106: メモリサイズは最低 8 * p_cost KiB 必要。
        let min_m_cost = self
            .p_cost
            .checked_mul(8)
            .ok_or(CryptoError::InvalidParameter)?;
        if self.m_cost < min_m_cost {
            return Err(CryptoError::InvalidParameter);
        }

        // argon2::Params の検証を直接実行して厳密な適合性を確認。
        Params::new(self.m_cost, self.t_cost, self.p_cost, Some(self.output_len))
            .map_err(|_| CryptoError::InvalidParameter)?;

        Ok(())
    }

    /// Wasm環境(シングルスレッド実行)への適合性を判定する。
    ///
    /// 並列度 `p_cost` が 1 の場合に真を返す。
    #[must_use]
    pub const fn is_wasm_compatible(&self) -> bool {
        self.p_cost == 1
    }

    /// 設定されているメモリコスト(KiB単位)を返す。
    #[must_use]
    pub const fn m_cost(&self) -> u32 {
        self.m_cost
    }

    /// 設定されている時間コスト(反復回数)を返す。
    #[must_use]
    pub const fn t_cost(&self) -> u32 {
        self.t_cost
    }

    /// 設定されている並列度(レーン数)を返す。
    #[must_use]
    pub const fn p_cost(&self) -> u32 {
        self.p_cost
    }

    /// 設定されている導出鍵長(バイト)を返す。
    #[must_use]
    pub const fn output_len(&self) -> usize {
        self.output_len
    }

    /// 設定されているアルゴリズム種別を返す。
    #[must_use]
    pub const fn algorithm(&self) -> Algorithm {
        self.algorithm
    }

    /// 設定されているバージョンを返す。
    #[must_use]
    pub const fn version(&self) -> Version {
        self.version
    }

    /// `argon2::Params` へ変換する。
    pub fn to_argon2_params(&self) -> Result<Params, CryptoError> {
        Params::new(self.m_cost, self.t_cost, self.p_cost, Some(self.output_len))
            .map_err(|_| CryptoError::InvalidParameter)
    }

    /// 指定されたパスワードとソルトから鍵を導出し、バッファ `out` に格納する。
    ///
    /// # エラー
    ///
    /// - `out` の長さが `self.output_len` と不一致、または短すぎる場合は [`CryptoError::InvalidKeySize`]。
    /// - パラメータが不正な場合は [`CryptoError::InvalidParameter`]。
    /// - 鍵導出処理中に障害が発生した場合は [`CryptoError::KeyDerivationFailed`]。
    pub fn derive_key(
        &self,
        password: &[u8],
        salt: &[u8],
        out: &mut [u8],
    ) -> Result<(), CryptoError> {
        self.derive_key_with_secret(password, salt, &[], out)
    }

    /// 指定されたペッパー(`secret`)と現在のパラメータから `Argon2` インスタンスを構築する。
    fn build_argon2<'a>(&self, secret: &'a [u8]) -> Result<Argon2<'a>, CryptoError> {
        let params = self.to_argon2_params()?;
        if secret.is_empty() {
            Ok(Argon2::new(self.algorithm, self.version, params))
        } else {
            Argon2::new_with_secret(secret, self.algorithm, self.version, params)
                .map_err(|_| CryptoError::InvalidParameter)
        }
    }

    /// 構築済み `Argon2` インスタンスで鍵を導出し、失敗時は出力バッファを即座にゼロクリアする。
    fn hash_into_buffer(
        argon2: &Argon2<'_>,
        password: &[u8],
        salt: &[u8],
        out: &mut [u8],
    ) -> Result<(), CryptoError> {
        if argon2.hash_password_into(password, salt, out).is_err() {
            crate::zeroize::volatile_zeroize(out);
            return Err(CryptoError::KeyDerivationFailed);
        }
        Ok(())
    }

    /// パスワード、ソルト、および秘密ペッパーから鍵を導出し、バッファ `out` に格納する。
    ///
    /// 鍵導出処理が失敗した場合は、部分的な書き込み残留を防ぐため出力バッファ `out` を即座にゼロクリアする。
    pub fn derive_key_with_secret(
        &self,
        password: &[u8],
        salt: &[u8],
        secret: &[u8],
        out: &mut [u8],
    ) -> Result<(), CryptoError> {
        if out.len() != self.output_len {
            return Err(CryptoError::InvalidKeySize);
        }

        let argon2 = self.build_argon2(secret)?;
        Self::hash_into_buffer(&argon2, password, salt, out)
    }

    /// 32バイト固定長の鍵を導出し、メモリゼロ消去が保証された [`SecretBytes<32>`] で返す。
    ///
    /// 本メソッドは `output_len == 32` のパラメータ設定を要求する。
    pub fn derive_key_32(
        &self,
        password: &[u8],
        salt: &[u8],
    ) -> Result<SecretBytes<32>, CryptoError> {
        self.derive_key_32_with_secret(password, salt, &[])
    }

    /// ペッパーを併用して32バイト固定長の鍵を導出し、[`SecretBytes<32>`] で返す。
    pub fn derive_key_32_with_secret(
        &self,
        password: &[u8],
        salt: &[u8],
        secret: &[u8],
    ) -> Result<SecretBytes<32>, CryptoError> {
        if self.output_len != 32 {
            return Err(CryptoError::InvalidKeySize);
        }

        let mut key_bytes = SecretBytes::<32>::zero();
        self.derive_key_with_secret(password, salt, secret, key_bytes.as_mut_slice())?;
        Ok(key_bytes)
    }

    /// 任意の出力長の鍵を導出し、メモリゼロ消去が保証された [`SecretVec`] で返す。
    #[cfg(feature = "alloc")]
    pub fn derive_key_vec(&self, password: &[u8], salt: &[u8]) -> Result<SecretVec, CryptoError> {
        self.derive_key_vec_with_secret(password, salt, &[])
    }

    /// ペッパーを併用して任意の出力長の鍵を導出し、[`SecretVec`] で返す。
    ///
    /// バッファは最初から [`SecretVec::zeroed`] として確保するため、
    /// 鍵導出途中でエラーやパニックが発生した場合でも RAII により確実にゼロ消去される。
    #[cfg(feature = "alloc")]
    pub fn derive_key_vec_with_secret(
        &self,
        password: &[u8],
        salt: &[u8],
        secret: &[u8],
    ) -> Result<SecretVec, CryptoError> {
        self.derive_key_vec_with_secret_fn(password, salt, secret, Self::hash_into_buffer)
    }

    /// テスト用フック: 出力用 [`SecretVec`] 確保後の鍵導出処理を差し替えて実行する。
    ///
    /// [`Self::derive_key_vec_with_secret`] と同一の事前検証、[`SecretVec::zeroed`] による
    /// ヒープ確保、および失敗時 RAII ゼロ消去経路を通るため、鍵導出失敗時のヒープ残留検証に利用できる。
    #[cfg(feature = "alloc")]
    #[doc(hidden)]
    pub fn derive_key_vec_with_secret_fn<F>(
        &self,
        password: &[u8],
        salt: &[u8],
        secret: &[u8],
        hash_fn: F,
    ) -> Result<SecretVec, CryptoError>
    where
        F: FnOnce(&Argon2<'_>, &[u8], &[u8], &mut [u8]) -> Result<(), CryptoError>,
    {
        let argon2 = self.build_argon2(secret)?;
        let mut key_vec = SecretVec::zeroed(self.output_len);
        hash_fn(&argon2, password, salt, key_vec.as_mut_slice())?;
        Ok(key_vec)
    }
}

/// RFC 5869 準拠の HKDF-SHA256 (Extract-and-Expand) により鍵を導出し、`out` へ格納する。
///
/// Extract 段階で生成された疑似乱数鍵 (PRK) は直ちに [`volatile_zeroize`] で消去し、
/// 出力長不正や Expand 失敗時は `out` 全体を即座にゼロクリアする。
///
/// # Errors
///
/// - `out` が空、または [`HKDF_SHA256_MAX_OUTPUT_LEN`] (8160バイト) を超える場合は、
///   [`CryptoError::InvalidKeySize`] を返す。
/// - Expand 処理に失敗した場合は [`CryptoError::KeyDerivationFailed`] を返す。
pub fn hkdf_sha256_derive(
    salt: &[u8],
    ikm: &[u8],
    info: &[u8],
    out: &mut [u8],
) -> Result<(), CryptoError> {
    if out.is_empty() || out.len() > HKDF_SHA256_MAX_OUTPUT_LEN {
        volatile_zeroize(out);
        return Err(CryptoError::InvalidKeySize);
    }

    let (mut prk, hk) = Hkdf::<Sha256>::extract(Some(salt), ikm);
    volatile_zeroize(prk.as_mut_slice());

    if hk.expand(info, out).is_err() {
        volatile_zeroize(out);
        return Err(CryptoError::KeyDerivationFailed);
    }

    Ok(())
}

/// RFC 5869 準拠の HKDF-SHA256 により 32バイト固定長の鍵を導出し、[`SecretBytes<32>`] で返す。
///
/// # Errors
///
/// 鍵導出処理に失敗した場合は [`CryptoError`] を返す。
pub fn hkdf_sha256_derive_32(
    salt: &[u8],
    ikm: &[u8],
    info: &[u8],
) -> Result<SecretBytes<32>, CryptoError> {
    let mut key = SecretBytes::<32>::zero();
    hkdf_sha256_derive(salt, ikm, info, key.as_mut_slice())?;
    Ok(key)
}

/// RFC 5869 準拠の HKDF-SHA256 により任意長 (`1..=8160` バイト) の鍵を導出し、[`SecretVec`] で返す。
///
/// # Errors
///
/// - `output_len` が `0` または [`HKDF_SHA256_MAX_OUTPUT_LEN`] を超える場合は、
///   ヒープ確保を行わずに [`CryptoError::InvalidKeySize`] を返す。
/// - 鍵導出処理に失敗した場合は [`CryptoError::KeyDerivationFailed`] を返す。
#[cfg(feature = "alloc")]
pub fn hkdf_sha256_derive_vec(
    salt: &[u8],
    ikm: &[u8],
    info: &[u8],
    output_len: usize,
) -> Result<SecretVec, CryptoError> {
    if output_len == 0 || output_len > HKDF_SHA256_MAX_OUTPUT_LEN {
        return Err(CryptoError::InvalidKeySize);
    }

    let mut key_vec = SecretVec::zeroed(output_len);
    hkdf_sha256_derive(salt, ikm, info, key_vec.as_mut_slice())?;
    Ok(key_vec)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_argon2_presets_and_wasm_compatibility() {
        let native = Argon2Params::for_native();
        assert_eq!(native.m_cost(), 65536, "Nativeメモリコストの照合に成功。");
        assert_eq!(native.t_cost(), 3, "Native時間コストの照合に成功。");
        assert_eq!(native.p_cost(), 4, "Native並列度の照合に成功。");
        assert_eq!(native.output_len(), 32, "Native鍵長の照合に成功。");
        assert!(
            !native.is_wasm_compatible(),
            "Native並列度4はWasm非互換と正しく判定に成功。"
        );

        let wasm = Argon2Params::for_wasm();
        assert_eq!(wasm.m_cost(), 19456, "Wasmメモリコストの照合に成功。");
        assert_eq!(wasm.t_cost(), 2, "Wasm時間コストの照合に成功。");
        assert_eq!(wasm.p_cost(), 1, "Wasm並列度の照合に成功。");
        assert!(
            wasm.is_wasm_compatible(),
            "Wasmシングルスレッド互換性判定に成功。"
        );

        let fast = Argon2Params::fast_test();
        assert_eq!(fast.m_cost(), 64, "テスト用メモリコストの照合に成功。");
        assert_eq!(fast.t_cost(), 1, "テスト用時間コストの照合に成功。");
        assert_eq!(fast.p_cost(), 1, "テスト用並列度の照合に成功。");
        assert!(
            fast.is_wasm_compatible(),
            "テスト用シングルスレッド互換性判定に成功。"
        );
    }

    #[test]
    fn test_argon2_default_selection() {
        let default_params = Argon2Params::default();
        #[cfg(target_arch = "wasm32")]
        {
            assert_eq!(
                default_params.p_cost(),
                1,
                "Wasm環境でシングルスレッドパラメータ自動選択に成功。"
            );
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            #[cfg(feature = "parallel")]
            {
                assert_eq!(
                    default_params.p_cost(),
                    4,
                    "Nativeかつparallel環境で並列度4自動選択に成功。"
                );
            }
            #[cfg(not(feature = "parallel"))]
            {
                assert_eq!(
                    default_params.p_cost(),
                    1,
                    "Nativeかつ非parallel環境でシングルスレッド自動選択に成功。"
                );
            }
        }
        assert!(
            default_params.validate().is_ok(),
            "既定パラメータ検証に成功。"
        );
    }

    #[test]
    fn test_argon2_parameter_validation() {
        // p_cost == 0
        let res = Argon2Params::custom(65536, 3, 0, Some(32));
        assert_eq!(
            res,
            Err(CryptoError::InvalidParameter),
            "並列度0の拒絶に成功。"
        );

        // t_cost == 0
        let res = Argon2Params::custom(65536, 0, 1, Some(32));
        assert_eq!(
            res,
            Err(CryptoError::InvalidParameter),
            "時間コスト0の拒絶に成功。"
        );

        // m_cost < 8 * p_cost (p_cost = 4, m_cost = 31 < 32)
        let res = Argon2Params::custom(31, 1, 4, Some(32));
        assert_eq!(
            res,
            Err(CryptoError::InvalidParameter),
            "最小メモリコスト制約違反の拒絶に成功。"
        );

        // 正常ケース
        let res = Argon2Params::custom(32, 1, 4, Some(32));
        assert!(res.is_ok(), "境界値パラメータ検証に成功。");
    }

    #[test]
    fn test_argon2_derive_key_and_secret_bytes() {
        let params = Argon2Params::fast_test();
        let password = b"master-password-test";
        let salt = b"unique-salt-12345678";

        let key1 = params.derive_key_32(password, salt);
        assert!(key1.is_ok(), "32バイト鍵導出に成功。");
        let key1 = key1.unwrap();

        // 同一入力に対する決定論的再現性
        let key2 = params.derive_key_32(password, salt).unwrap();
        assert_eq!(
            key1.as_slice(),
            key2.as_slice(),
            "同一パスワード・ソルトからの再現性検証に成功。"
        );

        // 異なるソルトに対する相違
        let diff_salt = b"unique-salt-87654321";
        let key3 = params.derive_key_32(password, diff_salt).unwrap();
        assert_ne!(
            key1.as_slice(),
            key3.as_slice(),
            "異なるソルトに対する相違性検証に成功。"
        );

        // 異なるパスワードに対する相違
        let diff_pwd = b"another-password-test";
        let key4 = params.derive_key_32(diff_pwd, salt).unwrap();
        assert_ne!(
            key1.as_slice(),
            key4.as_slice(),
            "異なるパスワードに対する相違性検証に成功。"
        );
    }

    #[test]
    fn test_argon2_derive_key_with_secret_pepper() {
        let params = Argon2Params::fast_test();
        let password = b"master-password-test";
        let salt = b"unique-salt-12345678";
        let pepper1 = b"server-side-pepper-01";
        let pepper2 = b"server-side-pepper-02";

        let key_without = params.derive_key_32(password, salt).unwrap();
        let key_with_1 = params
            .derive_key_32_with_secret(password, salt, pepper1)
            .unwrap();
        let key_with_2 = params
            .derive_key_32_with_secret(password, salt, pepper2)
            .unwrap();

        assert_ne!(
            key_without.as_slice(),
            key_with_1.as_slice(),
            "ペッパー有無による導出鍵変化の検証に成功。"
        );
        assert_ne!(
            key_with_1.as_slice(),
            key_with_2.as_slice(),
            "異なるペッパーによる導出鍵変化の検証に成功。"
        );
    }

    #[test]
    fn test_argon2_invalid_output_buffer_size() {
        let params = Argon2Params::fast_test();
        let password = b"password";
        let salt = b"salt-12345678";

        let mut short_buf = [0u8; 16];
        let res = params.derive_key(password, salt, &mut short_buf);
        assert_eq!(
            res,
            Err(CryptoError::InvalidKeySize),
            "不正出力バッファ長に対するエラー通知に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_argon2_derive_key_vec() {
        let params = Argon2Params::fast_test();
        let password = b"vec-password";
        let salt = b"vec-salt-123456";

        let key_vec = params.derive_key_vec(password, salt);
        assert!(key_vec.is_ok(), "SecretVecによる鍵導出に成功。");
        let key_vec = key_vec.unwrap();
        assert_eq!(key_vec.len(), 32, "導出ベクタ長の検証に成功。");

        // ペッパー指定時の導出結果の不一致および事前パラメータ検証を確認する。
        let peppered = params
            .derive_key_vec_with_secret(password, salt, b"pepper-secret")
            .unwrap();
        assert_ne!(
            key_vec.as_slice(),
            peppered.as_slice(),
            "ペッパー有無によるSecretVec導出鍵の変化に成功。"
        );

        // 過大な output_len 指定時でも事前検証でヒープ確保前に拒絶することを確認する。
        let oversized = Argon2Params::fast_test().with_output_len(usize::MAX);
        assert_eq!(
            oversized
                .derive_key_vec_with_secret(password, salt, &[])
                .err(),
            Some(CryptoError::InvalidParameter),
            "過大output_lenのヒープ確保前拒絶に成功。"
        );

        // 導出失敗時(ソルト長不足)のエラー返却を確認する。
        assert_eq!(
            params
                .derive_key_vec_with_secret(password, b"short", b"pepper")
                .err(),
            Some(CryptoError::KeyDerivationFailed),
            "不正ソルト長による鍵導出失敗の検証に成功。"
        );
    }

    #[test]
    fn test_argon2_derive_key_with_secret_zeroizes_on_failure() {
        let params = Argon2Params::fast_test();
        let mut out = [0xAAu8; 32];
        let res = params.derive_key_with_secret(b"password", b"short", b"pepper", &mut out);
        assert_eq!(
            res,
            Err(CryptoError::KeyDerivationFailed),
            "短すぎるソルトによる鍵導出失敗の確認に成功。"
        );
        assert_eq!(
            out, [0u8; 32],
            "鍵導出失敗時に出力バッファがゼロクリアされることの確認に成功。"
        );
    }

    #[test]
    fn test_argon2_reference_kat_single_thread() {
        // Argon2 Reference Implementation Known Answer Test (KAT)
        // Algorithm: Argon2id v0x13, t=2, m=256 KiB, p=1 (Single-thread)
        // Password: b"password", Salt: b"somesalt"
        let params = Argon2Params::custom(256, 2, 1, Some(32)).unwrap();
        assert!(params.is_wasm_compatible());

        let derived = params.derive_key_32(b"password", b"somesalt").unwrap();
        let expected_tag: [u8; 32] = [
            0x9d, 0xfe, 0xb9, 0x10, 0xe8, 0x0b, 0xad, 0x03, 0x11, 0xfe, 0xe2, 0x0f, 0x9c, 0x0e,
            0x2b, 0x12, 0xc1, 0x79, 0x87, 0xb4, 0xca, 0xc9, 0x0c, 0x2e, 0xf5, 0x4d, 0x5b, 0x30,
            0x21, 0xc6, 0x8b, 0xfe,
        ];

        assert_eq!(
            derived.as_slice(),
            &expected_tag,
            "Argon2idシングルスレッド公式テストベクタ照合に成功。"
        );
    }

    #[test]
    fn test_argon2_reference_kat_multi_lane_parallel() {
        // Argon2 Reference Implementation Known Answer Test (KAT)
        // Algorithm: Argon2id v0x13, t=2, m=256 KiB, p=2 (Multi-lane Parallel)
        // Password: b"password", Salt: b"somesalt"
        let params = Argon2Params::custom(256, 2, 2, Some(32)).unwrap();
        assert!(!params.is_wasm_compatible());

        let derived = params.derive_key_32(b"password", b"somesalt").unwrap();
        let expected_tag: [u8; 32] = [
            0x6d, 0x09, 0x3c, 0x50, 0x1f, 0xd5, 0x99, 0x96, 0x45, 0xe0, 0xea, 0x3b, 0xf6, 0x20,
            0xd7, 0xb8, 0xbe, 0x7f, 0xd2, 0xdb, 0x59, 0xc2, 0x0d, 0x9f, 0xff, 0x95, 0x39, 0xda,
            0x2b, 0xf5, 0x70, 0x37,
        ];

        assert_eq!(
            derived.as_slice(),
            &expected_tag,
            "Argon2idマルチレーン並列公式テストベクタ照合に成功。"
        );
    }

    #[test]
    fn test_argon2_builder_methods() {
        let wasm_custom_len = Argon2Params::for_wasm()
            .with_output_len(64)
            .validated()
            .expect("Wasm基準の出力長上書き検証に成功。");
        assert_eq!(wasm_custom_len.m_cost(), DEFAULT_WASM_M_COST);
        assert_eq!(wasm_custom_len.t_cost(), DEFAULT_WASM_T_COST);
        assert_eq!(wasm_custom_len.p_cost(), DEFAULT_WASM_P_COST);
        assert_eq!(wasm_custom_len.output_len(), 64);

        let native_custom = Argon2Params::for_native()
            .with_m_cost(131072)
            .with_t_cost(4)
            .with_p_cost(2)
            .with_output_len(48)
            .validated()
            .expect("Native基準の個別パラメータ上書き検証に成功。");
        assert_eq!(native_custom.m_cost(), 131072);
        assert_eq!(native_custom.t_cost(), 4);
        assert_eq!(native_custom.p_cost(), 2);
        assert_eq!(native_custom.output_len(), 48);

        assert_eq!(
            Argon2Params::for_wasm().with_output_len(0).validated(),
            Err(CryptoError::InvalidParameter),
            "不正な出力長0の拒絶に成功。"
        );
        assert_eq!(
            Argon2Params::for_native().with_m_cost(16).validated(),
            Err(CryptoError::InvalidParameter),
            "並列度に対する最小メモリコスト違反の拒絶に成功。"
        );
    }

    #[test]
    fn test_hkdf_sha256_rfc5869_kat_vectors() {
        // RFC 5869 Appendix A.1 (Test Case 1: Basic)
        let ikm1 = [0x0bu8; 22];
        let salt1 = [
            0x00u8, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
        ];
        let info1 = [0xf0u8, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9];
        let expected_okm1: [u8; 42] = [
            0x3c, 0xb2, 0x5f, 0x25, 0xfa, 0xac, 0xd5, 0x7a, 0x90, 0x43, 0x4f, 0x64, 0xd0, 0x36,
            0x2f, 0x2a, 0x2d, 0x2d, 0x0a, 0x90, 0xcf, 0x1a, 0x5a, 0x4c, 0x5d, 0xb0, 0x2d, 0x56,
            0xec, 0xc4, 0xc5, 0xbf, 0x34, 0x00, 0x72, 0x08, 0xd5, 0xb8, 0x87, 0x18, 0x58, 0x65,
        ];
        let mut okm1 = [0u8; 42];
        hkdf_sha256_derive(&salt1, &ikm1, &info1, &mut okm1).unwrap();
        // RFC 5869 Test Case 1 のテストベクターに一致することを確認。
        assert_eq!(okm1, expected_okm1);

        // RFC 5869 Appendix A.3 (Test Case 3: Zero-length salt/info)
        let ikm3 = [0x0bu8; 22];
        let expected_okm3: [u8; 42] = [
            0x8d, 0xa4, 0xe7, 0x75, 0xa5, 0x63, 0xc1, 0x8f, 0x71, 0x5f, 0x80, 0x2a, 0x06, 0x3c,
            0x5a, 0x31, 0xb8, 0xa1, 0x1f, 0x5c, 0x5e, 0xe1, 0x87, 0x9e, 0xc3, 0x45, 0x4e, 0x5f,
            0x3c, 0x73, 0x8d, 0x2d, 0x9d, 0x20, 0x13, 0x95, 0xfa, 0xa4, 0xb6, 0x1a, 0x96, 0xc8,
        ];
        let mut okm3 = [0u8; 42];
        hkdf_sha256_derive(&[], &ikm3, &[], &mut okm3).unwrap();
        // RFC 5869 Test Case 3 のテストベクターに一致することを確認。
        assert_eq!(okm3, expected_okm3);
    }

    #[test]
    fn test_hkdf_sha256_derive_32_and_error_handling() {
        let salt = b"vault-salt-1234567890";
        let ikm = [0x42u8; 32];
        let info = b"fidelogic-test-info";

        let key_a = hkdf_sha256_derive_32(salt, &ikm, info).unwrap();
        let key_b = hkdf_sha256_derive_32(salt, &ikm, info).unwrap();
        assert_eq!(key_a.as_slice(), key_b.as_slice());

        let key_diff_info = hkdf_sha256_derive_32(salt, &ikm, b"other-info").unwrap();
        assert_ne!(key_a.as_slice(), key_diff_info.as_slice());

        // 空出力長および上限超過時のエラー返却とゼロクリアの検証。
        let mut empty_out = [];
        assert_eq!(
            hkdf_sha256_derive(salt, &ikm, info, &mut empty_out),
            Err(CryptoError::InvalidKeySize)
        );

        let mut oversized = [0xAAu8; HKDF_SHA256_MAX_OUTPUT_LEN + 1];
        assert_eq!(
            hkdf_sha256_derive(salt, &ikm, info, &mut oversized),
            Err(CryptoError::InvalidKeySize)
        );
        // HKDF 出力長不正時における出力バッファのゼロ消去を確認。
        assert!(oversized.iter().all(|&b| b == 0));

        #[cfg(feature = "alloc")]
        {
            let vec_key = hkdf_sha256_derive_vec(salt, &ikm, info, 32).unwrap();
            assert_eq!(vec_key.as_slice(), key_a.as_slice());
            assert_eq!(
                hkdf_sha256_derive_vec(salt, &ikm, info, 0).err(),
                Some(CryptoError::InvalidKeySize)
            );
            assert_eq!(
                hkdf_sha256_derive_vec(salt, &ikm, info, HKDF_SHA256_MAX_OUTPUT_LEN + 1).err(),
                Some(CryptoError::InvalidKeySize)
            );
        }
    }
}
