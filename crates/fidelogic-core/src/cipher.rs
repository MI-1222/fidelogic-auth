//! # 暗号スイート抽象化モジュール。
//!
//! トレイトオブジェクトを排除した列挙型ディスパッチ([`VaultCipher`])により、
//! XChaCha20-Poly1305(192-bit Nonce)および AES-256-GCM-SIV(RFC 8452)の
//! 高速かつ静的インライン化が可能な暗号化・復号インターフェースを提供する。

use aes_gcm_siv::Aes256GcmSiv;
use aes_gcm_siv::aead::generic_array::GenericArray;
use aes_gcm_siv::aead::{AeadInPlace, KeyInit};
use chacha20poly1305::XChaCha20Poly1305;

use crate::error::CryptoError;
use crate::zeroize::SecretBytes;
#[cfg(feature = "alloc")]
use crate::zeroize::SecretVec;

/// 暗号鍵長(バイト単位: 256ビット = 32バイト)
pub const KEY_LEN: usize = 32;

/// XChaCha20-Poly1305 のノンス長(バイト単位: 192ビット = 24バイト)
pub const XCHACHA20_POLY1305_NONCE_LEN: usize = 24;

/// AES-256-GCM-SIV のノンス長(バイト単位: 96ビット = 12バイト)
pub const AES_256_GCM_SIV_NONCE_LEN: usize = 12;

/// 共通認証タグ長(バイト単位: 128ビット = 16バイト)
pub const TAG_LEN: usize = 16;

/// 暗号化可能な最大平文/暗号文ペイロード長(バイト単位)。
///
/// 認証タグ(16バイト)付加時の加算オーバーフロー(`len + TAG_LEN`)を防止し、
/// かつ 32-bit (Wasm) アーキテクチャおよび AEAD アルゴリズム規格(RFC 8439 / RFC 8452)の
/// アドレス空間制約を満たす安全上限値。
/// RFC 8452(AES-GCM-SIV)における平文/暗号文上限(2^36 - 31 バイト)に合わせて、
/// 64-bit 環境では 68,719,476,705 バイトに制限する。
#[cfg(target_pointer_width = "64")]
pub const MAX_PAYLOAD_LEN: usize = 68_719_476_705;
#[cfg(not(target_pointer_width = "64"))]
pub const MAX_PAYLOAD_LEN: usize = usize::MAX - TAG_LEN;

/// 関連データ(AAD: Associated Authenticated Data)の最大バイト長。
///
/// RFC 8452(AES-GCM-SIV)における AAD 上限(2^36 - 1 バイト)および
/// 32-bit 環境でのオーバーフローを防止する。
#[cfg(target_pointer_width = "64")]
pub const MAX_AAD_LEN: usize = 68_719_476_735;
#[cfg(not(target_pointer_width = "64"))]
pub const MAX_AAD_LEN: usize = usize::MAX;

/// ノンス長が指定された暗号スイートの要求長と一致するかを事前検証する。
#[inline]
pub fn validate_nonce_len(suite_id: CipherSuiteId, nonce: &[u8]) -> Result<(), CryptoError> {
    if nonce.len() != suite_id.nonce_len() {
        return Err(CryptoError::InvalidNonceSize);
    }
    Ok(())
}

/// 認証タグ長が 16 バイト([`TAG_LEN`])と一致するかを事前検証する。
#[inline]
pub fn validate_tag_len(tag: &[u8]) -> Result<(), CryptoError> {
    if tag.len() != TAG_LEN {
        return Err(CryptoError::InvalidTagSize);
    }
    Ok(())
}

/// 平文または暗号文スライス長が許容最大長およびオーバーフロー境界を満たすかを事前検証する。
#[inline]
pub fn validate_payload_len(payload: &[u8]) -> Result<(), CryptoError> {
    if payload.len() > MAX_PAYLOAD_LEN {
        return Err(CryptoError::InvalidSliceLength);
    }
    Ok(())
}

/// 関連データ(AAD)スライス長が許容上限を満たすかを事前検証する。
#[inline]
// 32-bit環境ではMAX_AAD_LENがusize::MAXとなり比較が恒偽になるが、環境非依存の単一コードパス維持のため許可する。
#[allow(clippy::absurd_extreme_comparisons)]
pub fn validate_aad_len(aad: &[u8]) -> Result<(), CryptoError> {
    if aad.len() > MAX_AAD_LEN {
        return Err(CryptoError::InvalidSliceLength);
    }
    Ok(())
}

/// 暗号スイート識別子を表す列挙型。
///
/// Vaultヘッダーの `suite_id` フィールド(1バイト)に対応し、
/// 暗号化アルゴリズムおよびノンス長を一意に決定する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum CipherSuiteId {
    /// XChaCha20-Poly1305 (256-bit Key, 192-bit Nonce, 128-bit Tag)。
    XChaCha20Poly1305 = 0x01,
    /// AES-256-GCM-SIV (RFC 8452, 256-bit Key, 96-bit Nonce, 128-bit Tag)。
    Aes256GcmSiv = 0x02,
}

impl CipherSuiteId {
    /// 1バイト整数から [`CipherSuiteId`] への変換を試みる。
    #[inline]
    pub const fn from_u8(value: u8) -> Result<Self, CryptoError> {
        match value {
            0x01 => Ok(Self::XChaCha20Poly1305),
            0x02 => Ok(Self::Aes256GcmSiv),
            _ => Err(CryptoError::InvalidParameter),
        }
    }

    /// 暗号スイート識別子の数値(`u8`)を返す。
    #[inline]
    pub const fn as_u8(self) -> u8 {
        self as u8
    }

    /// 本暗号スイートで要求されるノンス長(バイト数)を返す。
    #[inline]
    pub const fn nonce_len(self) -> usize {
        match self {
            Self::XChaCha20Poly1305 => XCHACHA20_POLY1305_NONCE_LEN,
            Self::Aes256GcmSiv => AES_256_GCM_SIV_NONCE_LEN,
        }
    }

    /// 本暗号スイートで要求される認証タグ長(バイト数)を返す。
    #[inline]
    pub const fn tag_len(self) -> usize {
        TAG_LEN
    }

    /// 本暗号スイートで要求される鍵長(バイト数)を返す。
    #[inline]
    pub const fn key_len(self) -> usize {
        KEY_LEN
    }
}

impl TryFrom<u8> for CipherSuiteId {
    type Error = CryptoError;

    #[inline]
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::from_u8(value)
    }
}

impl From<CipherSuiteId> for u8 {
    #[inline]
    fn from(suite: CipherSuiteId) -> Self {
        suite.as_u8()
    }
}

/// 暗号化コンテナで使用されるAEAD暗号スイートの列挙型ディスパッチ構造体。
///
/// トレイトオブジェクト(`dyn AeadInPlace`)による間接呼び出しオーバーヘッドや
/// vtableメタデータの保持を完全に排除し、静的インライン化およびゼロコストディスパッチを実現する。
/// ヒープ確保(`Box`)を排して `no_std` 環境でのゼロアロケーション運用を維持するため、
/// バリアント間サイズ差の警告を抑制している。
#[allow(clippy::large_enum_variant)]
pub enum VaultCipher {
    /// XChaCha20-Poly1305 暗号インスタンス。
    XChaCha20Poly1305(XChaCha20Poly1305),
    /// AES-256-GCM-SIV 暗号インスタンス。
    Aes256GcmSiv(Aes256GcmSiv),
}

impl Drop for VaultCipher {
    #[inline]
    fn drop(&mut self) {
        // バリアント内部の XChaCha20Poly1305 および Aes256GcmSiv(内部の aes::Aes256) は、
        // 本 Drop 完了後に実行される各フィールドの Drop により保持する鍵・拡張ラウンド鍵をゼロ消去する。
    }
}

impl zeroize::ZeroizeOnDrop for VaultCipher {}

const _: fn() = || {
    fn assert_zeroize_on_drop<T: zeroize::ZeroizeOnDrop>() {}
    assert_zeroize_on_drop::<XChaCha20Poly1305>();
    assert_zeroize_on_drop::<aes::Aes256>();
    assert_zeroize_on_drop::<VaultCipher>();
};

impl VaultCipher {
    /// 32バイト固定長秘密鍵配列および暗号スイート識別子から暗号インスタンスを生成する。
    #[inline]
    pub fn new(suite_id: CipherSuiteId, key: &[u8; KEY_LEN]) -> Self {
        let key_arr = GenericArray::from_slice(key);
        match suite_id {
            CipherSuiteId::XChaCha20Poly1305 => {
                Self::XChaCha20Poly1305(XChaCha20Poly1305::new(key_arr))
            }
            CipherSuiteId::Aes256GcmSiv => Self::Aes256GcmSiv(Aes256GcmSiv::new(key_arr)),
        }
    }

    /// [`SecretBytes<32>`] から暗号インスタンスを安全に生成する。
    #[inline]
    pub fn new_from_secret(suite_id: CipherSuiteId, key: &SecretBytes<KEY_LEN>) -> Self {
        Self::new(suite_id, key.as_bytes())
    }

    /// 任意長スライスから鍵長(32バイト)を事前検証して暗号インスタンスを生成する。
    ///
    /// 鍵長が 32 バイトでない場合はパニックさせず、直ちに [`CryptoError::InvalidKeySize`] を返却する。
    #[inline]
    pub fn new_from_slice(suite_id: CipherSuiteId, key: &[u8]) -> Result<Self, CryptoError> {
        let key_arr: &[u8; KEY_LEN] = key.try_into().map_err(|_| CryptoError::InvalidKeySize)?;
        Ok(Self::new(suite_id, key_arr))
    }

    /// 本暗号インスタンスの暗号スイート識別子を返す。
    #[inline]
    pub const fn suite_id(&self) -> CipherSuiteId {
        match self {
            Self::XChaCha20Poly1305(_) => CipherSuiteId::XChaCha20Poly1305,
            Self::Aes256GcmSiv(_) => CipherSuiteId::Aes256GcmSiv,
        }
    }

    /// 本暗号インスタンスで要求されるノンス長(バイト数)を返す。
    #[inline]
    pub const fn nonce_len(&self) -> usize {
        self.suite_id().nonce_len()
    }

    /// 本暗号インスタンスで要求される認証タグ長(バイト数)を返す。
    #[inline]
    pub const fn tag_len(&self) -> usize {
        self.suite_id().tag_len()
    }

    /// インプレース分離暗号化(Detached Encryption)を実行し、16バイトの認証タグを返す。
    ///
    /// `buffer` に平文を渡すと暗号文に上書きされ、計算された16バイトの認証タグが返される。
    ///
    /// # パニックフリー性と安全検証
    /// - ノンス長が暗号スイートの要求長と一致しない場合は [`CryptoError::InvalidNonceSize`] を返す。
    /// - 平文バッファ長が [`MAX_PAYLOAD_LEN`] を超過またはタグ加算でオーバーフローする場合は [`CryptoError::InvalidSliceLength`] を返す。
    /// - AAD長が [`MAX_AAD_LEN`] を超過する場合は [`CryptoError::InvalidSliceLength`] を返す。
    /// - 開始前の引数検証エラー時は呼び出し元バッファを変更せずにエラーを返却し、再試行を可能とする。
    /// - 暗号化処理自体の失敗時は、部分的な書き換え残留を防ぐためバッファを直ちに [`crate::zeroize::volatile_zeroize`] で
    ///   ゼロクリアし、[`CryptoError::AeadEncryptionFailed`] 等を返す。
    pub fn encrypt_in_place_detached(
        &self,
        nonce: &[u8],
        aad: &[u8],
        buffer: &mut [u8],
    ) -> Result<[u8; TAG_LEN], CryptoError> {
        validate_nonce_len(self.suite_id(), nonce)?;
        validate_payload_len(buffer)?;
        validate_aad_len(aad)?;

        let tag = match self {
            Self::XChaCha20Poly1305(cipher) => {
                let nonce_arr = GenericArray::from_slice(nonce);
                cipher
                    .encrypt_in_place_detached(nonce_arr, aad, buffer)
                    .map_err(|_| {
                        crate::zeroize::volatile_zeroize(buffer);
                        CryptoError::AeadEncryptionFailed
                    })?
            }
            Self::Aes256GcmSiv(cipher) => {
                let nonce_arr = GenericArray::from_slice(nonce);
                cipher
                    .encrypt_in_place_detached(nonce_arr, aad, buffer)
                    .map_err(|_| {
                        crate::zeroize::volatile_zeroize(buffer);
                        CryptoError::AeadEncryptionFailed
                    })?
            }
        };

        Ok(tag.into())
    }

    /// インプレース分離復号(Detached Decryption)を実行する。
    ///
    /// `buffer` に暗号文を渡し、`tag` に16バイトの認証タグを渡すと、認証成功時に平文へ上書きされる。
    /// 内部的にはスライス長を一度だけ検証して固定長配列へ変換し、
    /// [`Self::decrypt_in_place_detached_tag`] へ委譲する。
    ///
    /// # パニックフリー性と安全検証
    /// - 認証タグ長が 16 バイトでない場合は [`CryptoError::InvalidTagSize`] を返す。
    /// - ノンス長が不一致の場合は [`CryptoError::InvalidNonceSize`] を返す。
    /// - 暗号文バッファ長が [`MAX_PAYLOAD_LEN`] を超過する場合は [`CryptoError::InvalidSliceLength`] を返す。
    /// - AAD長が [`MAX_AAD_LEN`] を超過する場合は [`CryptoError::InvalidSliceLength`] を返す。
    /// - 開始前の引数検証エラー時は呼び出し元バッファを変更せずにエラーを返却し、再試行を可能とする。
    /// - 認証タグ不一致または復号処理自体の失敗時は、部分的な復号データの残留を防ぐためバッファを直ちに
    ///   [`crate::zeroize::volatile_zeroize`] でゼロクリアし、[`CryptoError::AeadDecryptionFailed`] を返す。
    #[inline]
    pub fn decrypt_in_place_detached(
        &self,
        nonce: &[u8],
        aad: &[u8],
        buffer: &mut [u8],
        tag: &[u8],
    ) -> Result<(), CryptoError> {
        let tag_arr: &[u8; TAG_LEN] = tag.try_into().map_err(|_| CryptoError::InvalidTagSize)?;

        self.decrypt_in_place_detached_tag(nonce, aad, buffer, tag_arr)
    }

    /// 固定長配列 `[u8; TAG_LEN]` の認証タグを用いてインプレース分離復号を実行する。
    ///
    /// コンパイル時の型システムによりタグ長が 16 バイトであることが保証され、
    /// タグ長不一致によるランタイム検査・分岐および境界外アクセスを構造的に排除する。
    ///
    /// # パニックフリー性と安全検証
    /// - ノンス長が不一致の場合は [`CryptoError::InvalidNonceSize`] を返す。
    /// - 暗号文バッファ長が [`MAX_PAYLOAD_LEN`] を超過する場合は [`CryptoError::InvalidSliceLength`] を返す。
    /// - AAD長が [`MAX_AAD_LEN`] を超過する場合は [`CryptoError::InvalidSliceLength`] を返す。
    /// - 開始前の引数検証エラー時は呼び出し元バッファを変更せずにエラーを返却し、再試行を可能とする。
    /// - 認証タグ不一致または復号処理自体の失敗時は、部分的な復号データの残留を防ぐためバッファを直ちに
    ///   [`crate::zeroize::volatile_zeroize`] でゼロクリアし、[`CryptoError::AeadDecryptionFailed`] を返す。
    pub fn decrypt_in_place_detached_tag(
        &self,
        nonce: &[u8],
        aad: &[u8],
        buffer: &mut [u8],
        tag: &[u8; TAG_LEN],
    ) -> Result<(), CryptoError> {
        validate_nonce_len(self.suite_id(), nonce)?;
        validate_payload_len(buffer)?;
        validate_aad_len(aad)?;

        let tag_arr = GenericArray::from_slice(tag);
        let result = match self {
            Self::XChaCha20Poly1305(cipher) => {
                let nonce_arr = GenericArray::from_slice(nonce);
                cipher.decrypt_in_place_detached(nonce_arr, aad, buffer, tag_arr)
            }
            Self::Aes256GcmSiv(cipher) => {
                let nonce_arr = GenericArray::from_slice(nonce);
                cipher.decrypt_in_place_detached(nonce_arr, aad, buffer, tag_arr)
            }
        };

        result.map_err(|_| {
            crate::zeroize::volatile_zeroize(buffer);
            CryptoError::AeadDecryptionFailed
        })
    }

    /// 平文全体を暗号化し、暗号文の末尾に16バイトの認証タグを付与したバイト列(Ciphertext || Tag)を返す。
    ///
    /// ヒープ割り当てを伴わないゼロコストなメインストリームとして、
    /// 通常は [`Self::encrypt_in_place_detached`] の利用を推奨する。
    /// 本メソッドは `alloc` 環境向けの利便性補助APIである。
    ///
    /// # パニックフリー性と安全検証
    /// - ノンス長、平文長、および AAD 長を事前に検証し、加算オーバーフローや境界外スライシングを防止する。
    /// - 暗号化失敗時は確保された一時バッファを直ちにゼロクリアし、秘密情報の残留を防ぐ。
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn encrypt(
        &self,
        nonce: &[u8],
        plaintext: &[u8],
        aad: &[u8],
    ) -> Result<alloc::vec::Vec<u8>, CryptoError> {
        self.encrypt_with_detached(nonce, plaintext, aad, |cipher, n, a, buf| {
            cipher.encrypt_in_place_detached(n, a, buf)
        })
    }

    /// テスト用フック: バッファ確保後のインプレース暗号化処理を差し替えて実行する。
    ///
    /// [`Self::encrypt`] と同一の事前検証、ヒープ確保、および失敗時ゼロ消去経路を通るため、
    /// 暗号化プリミティブ失敗時のヒープ残留検証に利用できる。
    #[cfg(feature = "alloc")]
    #[doc(hidden)]
    pub fn encrypt_with_detached<F>(
        &self,
        nonce: &[u8],
        plaintext: &[u8],
        aad: &[u8],
        encrypt_detached: F,
    ) -> Result<alloc::vec::Vec<u8>, CryptoError>
    where
        F: FnOnce(&Self, &[u8], &[u8], &mut [u8]) -> Result<[u8; TAG_LEN], CryptoError>,
    {
        validate_nonce_len(self.suite_id(), nonce)?;
        validate_payload_len(plaintext)?;
        validate_aad_len(aad)?;

        let total_len = plaintext
            .len()
            .checked_add(TAG_LEN)
            .ok_or(CryptoError::InvalidSliceLength)?;

        let mut buffer = zeroize::Zeroizing::new(alloc::vec::Vec::with_capacity(total_len));
        buffer.extend_from_slice(plaintext);

        let tag = match encrypt_detached(self, nonce, aad, &mut buffer) {
            Ok(tag) => tag,
            Err(err) => {
                crate::zeroize::volatile_zeroize(&mut buffer);
                return Err(err);
            }
        };

        buffer.extend_from_slice(&tag);
        Ok(core::mem::take(&mut *buffer))
    }

    /// 認証タグ付き暗号文(Ciphertext || Tag)を復号し、Drop時自動ゼロ消去が保証された [`SecretVec`] を返す。
    ///
    /// ヒープ割り当てや平文コピー自体を排除するゼロコストかつ安全なメインストリームとして、
    /// 通常はインプレース復号([`Self::decrypt_in_place_detached`] または [`Self::decrypt_in_place_detached_tag`])の利用を推奨する。
    /// 本メソッドは `alloc` 環境向けの利便性補助APIであり、返却した平文バッファの破棄時に
    /// [`SecretVec`] によってメモリが自動的にゼロ消去される。
    ///
    /// # パニックフリー性と安全検証
    /// - 入力長がタグ長(`TAG_LEN = 16`)未満の場合はパニックせず直ちに [`CryptoError::InvalidTagSize`] を返す。
    /// - スライス分割には `get()` による安全なインデックス参照を用い、境界外トラップを排除する。
    /// - バッファ確保前にノンス長、暗号文長、AAD長を検証し、不正入力による無駄なヒープ割り当てを防ぐ。
    /// - 復号失敗時は [`SecretVec`] 内の平文候補バッファを即座にゼロクリアした上でエラーを返す。
    #[cfg(feature = "alloc")]
    pub fn decrypt(
        &self,
        nonce: &[u8],
        ciphertext_with_tag: &[u8],
        aad: &[u8],
    ) -> Result<SecretVec, CryptoError> {
        let split_idx = ciphertext_with_tag
            .len()
            .checked_sub(TAG_LEN)
            .ok_or(CryptoError::InvalidTagSize)?;

        let ct_slice = ciphertext_with_tag
            .get(..split_idx)
            .ok_or(CryptoError::InvalidSliceLength)?;
        let tag = ciphertext_with_tag
            .get(split_idx..)
            .ok_or(CryptoError::InvalidTagSize)?;
        let tag_arr: &[u8; TAG_LEN] = tag.try_into().map_err(|_| CryptoError::InvalidTagSize)?;

        validate_nonce_len(self.suite_id(), nonce)?;
        validate_payload_len(ct_slice)?;
        validate_aad_len(aad)?;

        let mut buffer = SecretVec::from_slice(ct_slice);

        self.decrypt_in_place_detached_tag(nonce, aad, buffer.as_mut_slice(), tag_arr)?;

        Ok(buffer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cipher_suite_id_conversions() {
        assert_eq!(
            CipherSuiteId::from_u8(1),
            Ok(CipherSuiteId::XChaCha20Poly1305),
            "suite_id 0x01のパースに成功。"
        );
        assert_eq!(
            CipherSuiteId::from_u8(2),
            Ok(CipherSuiteId::Aes256GcmSiv),
            "suite_id 0x02のパースに成功。"
        );
        assert_eq!(
            CipherSuiteId::from_u8(0),
            Err(CryptoError::InvalidParameter),
            "不正なsuite_id 0の拒絶に成功。"
        );
        assert_eq!(
            CipherSuiteId::from_u8(3),
            Err(CryptoError::InvalidParameter),
            "不正なsuite_id 3の拒絶に成功。"
        );

        assert_eq!(
            CipherSuiteId::XChaCha20Poly1305.as_u8(),
            1,
            "XChaCha20Poly1305の数値変換に成功。"
        );
        assert_eq!(
            CipherSuiteId::Aes256GcmSiv.as_u8(),
            2,
            "Aes256GcmSivの数値変換に成功。"
        );

        assert_eq!(
            CipherSuiteId::try_from(1),
            Ok(CipherSuiteId::XChaCha20Poly1305),
            "TryFromによる変換に成功。"
        );
        let u8_val: u8 = CipherSuiteId::Aes256GcmSiv.into();
        assert_eq!(u8_val, 2, "Fromによる変換に成功。");

        assert_eq!(
            CipherSuiteId::XChaCha20Poly1305.nonce_len(),
            24,
            "XChaCha20Poly1305ノンス長24バイトの確認に成功。"
        );
        assert_eq!(
            CipherSuiteId::Aes256GcmSiv.nonce_len(),
            12,
            "Aes256GcmSivノンス長12バイトの確認に成功。"
        );
        assert_eq!(
            CipherSuiteId::XChaCha20Poly1305.tag_len(),
            16,
            "タグ長16バイトの確認に成功。"
        );
        assert_eq!(
            CipherSuiteId::Aes256GcmSiv.tag_len(),
            16,
            "タグ長16バイトの確認に成功。"
        );
        assert_eq!(
            CipherSuiteId::XChaCha20Poly1305.key_len(),
            32,
            "鍵長32バイトの確認に成功。"
        );
    }

    #[test]
    fn test_vault_cipher_constructors() {
        let key = [0x42u8; KEY_LEN];
        let cipher_x = VaultCipher::new(CipherSuiteId::XChaCha20Poly1305, &key);
        assert_eq!(
            cipher_x.suite_id(),
            CipherSuiteId::XChaCha20Poly1305,
            "XChaCha暗号インスタンス生成に成功。"
        );
        assert_eq!(cipher_x.nonce_len(), 24, "XChaChaノンス長照合に成功。");
        assert_eq!(cipher_x.tag_len(), 16, "XChaChaタグ長照合に成功。");

        let cipher_aes = VaultCipher::new(CipherSuiteId::Aes256GcmSiv, &key);
        assert_eq!(
            cipher_aes.suite_id(),
            CipherSuiteId::Aes256GcmSiv,
            "AES-GCM-SIV暗号インスタンス生成に成功。"
        );
        assert_eq!(cipher_aes.nonce_len(), 12, "AESノンス長照合に成功。");
        assert_eq!(cipher_aes.tag_len(), 16, "AESタグ長照合に成功。");

        let secret = SecretBytes::new(key);
        let cipher_secret = VaultCipher::new_from_secret(CipherSuiteId::XChaCha20Poly1305, &secret);
        assert_eq!(
            cipher_secret.suite_id(),
            CipherSuiteId::XChaCha20Poly1305,
            "SecretBytes経由の生成に成功。"
        );

        let slice_ok = VaultCipher::new_from_slice(CipherSuiteId::Aes256GcmSiv, &key[..]);
        assert!(slice_ok.is_ok(), "スライス経由の正常生成に成功。");

        let short_key = [0x42u8; 31];
        let slice_err = VaultCipher::new_from_slice(CipherSuiteId::Aes256GcmSiv, &short_key[..]);
        assert_eq!(
            slice_err.err(),
            Some(CryptoError::InvalidKeySize),
            "短小鍵スライスの拒絶に成功。"
        );
    }

    #[test]
    fn test_xchacha20_poly1305_roundtrip_and_tamper() {
        let key = [0x11u8; KEY_LEN];
        let nonce = [0x22u8; XCHACHA20_POLY1305_NONCE_LEN];
        let aad = b"header-aad-metadata";
        let plaintext_original = b"Fidelogic Secure Vault Secret Plaintext Data";

        let cipher = VaultCipher::new(CipherSuiteId::XChaCha20Poly1305, &key);

        let mut buffer = *plaintext_original;
        let tag = cipher
            .encrypt_in_place_detached(&nonce, aad, &mut buffer)
            .expect("暗号化に成功。");

        assert_ne!(
            buffer.as_slice(),
            plaintext_original.as_slice(),
            "暗号文が平文と相違することを確認。"
        );

        // 正常復号
        let mut decrypt_buf = buffer;
        cipher
            .decrypt_in_place_detached(&nonce, aad, &mut decrypt_buf, &tag)
            .expect("復号に成功。");
        assert_eq!(
            decrypt_buf.as_slice(),
            plaintext_original.as_slice(),
            "平文の完全復元に成功。"
        );

        // 改ざん暗号文の拒絶
        let mut tampered_buf = buffer;
        tampered_buf[0] ^= 0x01;
        let res_tampered = cipher.decrypt_in_place_detached(&nonce, aad, &mut tampered_buf, &tag);
        assert_eq!(
            res_tampered,
            Err(CryptoError::AeadDecryptionFailed),
            "改ざん暗号文の拒絶に成功。"
        );
        assert_eq!(
            tampered_buf, [0u8; 44],
            "改ざん検知時のバッファ揮発ゼロクリアに成功。"
        );

        // 改ざんタグの拒絶
        let mut decrypt_buf2 = buffer;
        let mut tampered_tag = tag;
        tampered_tag[0] ^= 0x01;
        let res_tag =
            cipher.decrypt_in_place_detached(&nonce, aad, &mut decrypt_buf2, &tampered_tag);
        assert_eq!(
            res_tag,
            Err(CryptoError::AeadDecryptionFailed),
            "改ざんタグの拒絶に成功。"
        );

        // 改ざんAADの拒絶
        let mut decrypt_buf3 = buffer;
        let tampered_aad = b"tampered-aad-metadata";
        let res_aad =
            cipher.decrypt_in_place_detached(&nonce, tampered_aad, &mut decrypt_buf3, &tag);
        assert_eq!(
            res_aad,
            Err(CryptoError::AeadDecryptionFailed),
            "改ざんAADの拒絶に成功。"
        );

        // 不正なノンス長
        let invalid_nonce = [0x22u8; 12];
        let mut dummy = [0u8; 10];
        assert_eq!(
            cipher.encrypt_in_place_detached(&invalid_nonce, aad, &mut dummy),
            Err(CryptoError::InvalidNonceSize),
            "不正ノンス長の暗号化拒絶に成功。"
        );
        assert_eq!(
            cipher.decrypt_in_place_detached(&invalid_nonce, aad, &mut dummy, &tag),
            Err(CryptoError::InvalidNonceSize),
            "不正ノンス長の復号拒絶に成功。"
        );

        // 不正なタグ長
        let invalid_tag = [0u8; 15];
        assert_eq!(
            cipher.decrypt_in_place_detached(&nonce, aad, &mut decrypt_buf, &invalid_tag),
            Err(CryptoError::InvalidTagSize),
            "不正タグ長の復号拒絶に成功。"
        );
    }

    #[test]
    fn test_aes256_gcm_siv_roundtrip_and_tamper() {
        let key = [0x33u8; KEY_LEN];
        let nonce = [0x44u8; AES_256_GCM_SIV_NONCE_LEN];
        let aad = b"epoch-epoch-counter-12345";
        let plaintext_original = b"Synthetic IV Nonce Misuse-Resistant Plaintext";

        let cipher = VaultCipher::new(CipherSuiteId::Aes256GcmSiv, &key);

        let mut buffer = *plaintext_original;
        let tag = cipher
            .encrypt_in_place_detached(&nonce, aad, &mut buffer)
            .expect("暗号化に成功。");

        assert_ne!(
            buffer.as_slice(),
            plaintext_original.as_slice(),
            "暗号文が平文と相違することを確認。"
        );

        // 正常復号
        let mut decrypt_buf = buffer;
        cipher
            .decrypt_in_place_detached(&nonce, aad, &mut decrypt_buf, &tag)
            .expect("復号に成功。");
        assert_eq!(
            decrypt_buf.as_slice(),
            plaintext_original.as_slice(),
            "平文の完全復元に成功。"
        );

        // 改ざん暗号文の拒絶
        let mut tampered_buf = buffer;
        tampered_buf[0] ^= 0x01;
        let res_tampered = cipher.decrypt_in_place_detached(&nonce, aad, &mut tampered_buf, &tag);
        assert_eq!(
            res_tampered,
            Err(CryptoError::AeadDecryptionFailed),
            "改ざん暗号文の拒絶に成功。"
        );
        assert_eq!(
            tampered_buf, [0u8; 45],
            "改ざん検知時のバッファ揮発ゼロクリアに成功。"
        );

        // 改ざんタグの拒絶
        let mut decrypt_buf2 = buffer;
        let mut tampered_tag = tag;
        tampered_tag[0] ^= 0x01;
        let res_tag =
            cipher.decrypt_in_place_detached(&nonce, aad, &mut decrypt_buf2, &tampered_tag);
        assert_eq!(
            res_tag,
            Err(CryptoError::AeadDecryptionFailed),
            "改ざんタグの拒絶に成功。"
        );

        // 改ざんAADの拒絶
        let mut decrypt_buf3 = buffer;
        let tampered_aad = b"tampered-epoch-counter-00000";
        let res_aad =
            cipher.decrypt_in_place_detached(&nonce, tampered_aad, &mut decrypt_buf3, &tag);
        assert_eq!(
            res_aad,
            Err(CryptoError::AeadDecryptionFailed),
            "改ざんAADの拒絶に成功。"
        );

        // 不正なノンス長
        let invalid_nonce = [0x44u8; 24];
        let mut dummy = [0u8; 10];
        assert_eq!(
            cipher.encrypt_in_place_detached(&invalid_nonce, aad, &mut dummy),
            Err(CryptoError::InvalidNonceSize),
            "不正ノンス長の暗号化拒絶に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_alloc_encrypt_decrypt_convenience_apis() {
        let key = [0x77u8; KEY_LEN];
        let nonce_x = [0x88u8; XCHACHA20_POLY1305_NONCE_LEN];
        let nonce_aes = [0x99u8; AES_256_GCM_SIV_NONCE_LEN];
        let aad = b"convenience-aad";
        let plaintext = b"Arbitrary Dynamic Plaintext Buffer for Testing Alloc APIs";

        // XChaCha20Poly1305
        let cipher_x = VaultCipher::new(CipherSuiteId::XChaCha20Poly1305, &key);
        let ct_x = cipher_x
            .encrypt(&nonce_x, plaintext, aad)
            .expect("alloc暗号化に成功。");
        assert_eq!(
            ct_x.len(),
            plaintext.len() + TAG_LEN,
            "暗号文長の検証に成功。"
        );
        let pt_x: SecretVec = cipher_x
            .decrypt(&nonce_x, &ct_x, aad)
            .expect("alloc復号に成功。");
        assert_eq!(pt_x.as_slice(), plaintext, "復号平文の一致に成功。");

        // AES-256-GCM-SIV
        let cipher_aes = VaultCipher::new(CipherSuiteId::Aes256GcmSiv, &key);
        let ct_aes = cipher_aes
            .encrypt(&nonce_aes, plaintext, aad)
            .expect("alloc暗号化に成功。");
        assert_eq!(
            ct_aes.len(),
            plaintext.len() + TAG_LEN,
            "暗号文長の検証に成功。"
        );
        let pt_aes: SecretVec = cipher_aes
            .decrypt(&nonce_aes, &ct_aes, aad)
            .expect("alloc復号に成功。");
        assert_eq!(pt_aes.as_slice(), plaintext, "復号平文の一致に成功。");

        // 改ざん暗号文の拒絶
        let mut tampered_ct = ct_aes.clone();
        tampered_ct[0] ^= 0x01;
        assert_eq!(
            cipher_aes.decrypt(&nonce_aes, &tampered_ct, aad).err(),
            Some(CryptoError::AeadDecryptionFailed),
            "改ざん暗号文の拒絶に成功。"
        );

        // 不正タグ長の拒絶
        let short_ct = alloc::vec![0u8; TAG_LEN - 1];
        assert_eq!(
            cipher_aes.decrypt(&nonce_aes, &short_ct, aad).err(),
            Some(CryptoError::InvalidTagSize),
            "短小暗号文の拒絶に成功。"
        );
    }

    #[test]
    fn test_rfc8452_aes256_gcm_siv_kat_vectors() {
        // RFC 8452 Appendix C.2 (256-bit Key) Example 1:
        // Plaintext: empty, AAD: empty
        let key_ex1: [u8; KEY_LEN] = [
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let nonce_ex1: [u8; AES_256_GCM_SIV_NONCE_LEN] = [
            0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];
        let expected_tag_ex1: [u8; TAG_LEN] = [
            0x07, 0xf5, 0xf4, 0x16, 0x9b, 0xbf, 0x55, 0xa8, 0x40, 0x0c, 0xd4, 0x7e, 0xa6, 0xfd,
            0x40, 0x0f,
        ];

        let cipher_ex1 = VaultCipher::new(CipherSuiteId::Aes256GcmSiv, &key_ex1);
        let mut buf_ex1: [u8; 0] = [];
        let tag_ex1 = cipher_ex1
            .encrypt_in_place_detached(&nonce_ex1, &[], &mut buf_ex1)
            .expect("RFC 8452 Example 1 暗号化に成功。");
        assert_eq!(
            tag_ex1, expected_tag_ex1,
            "RFC 8452 Example 1 認証タグ突合に成功。"
        );

        // RFC 8452 Appendix C.2 Example 4:
        // Plaintext: 16 bytes, AAD: empty
        let plaintext_ex4: [u8; 16] = [
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00,
        ];
        let expected_ct_ex4: [u8; 16] = [
            0x85, 0xa0, 0x1b, 0x63, 0x02, 0x5b, 0xa1, 0x9b, 0x7f, 0xd3, 0xdd, 0xfc, 0x03, 0x3b,
            0x3e, 0x76,
        ];
        let expected_tag_ex4: [u8; TAG_LEN] = [
            0xc9, 0xea, 0xc6, 0xfa, 0x70, 0x09, 0x42, 0x70, 0x2e, 0x90, 0x86, 0x23, 0x83, 0xc6,
            0xc3, 0x66,
        ];

        let mut buf_ex4 = plaintext_ex4;
        let tag_ex4 = cipher_ex1
            .encrypt_in_place_detached(&nonce_ex1, &[], &mut buf_ex4)
            .expect("RFC 8452 Example 4 暗号化に成功。");
        assert_eq!(
            buf_ex4, expected_ct_ex4,
            "RFC 8452 Example 4 暗号文突合に成功。"
        );
        assert_eq!(
            tag_ex4, expected_tag_ex4,
            "RFC 8452 Example 4 認証タグ突合に成功。"
        );

        // 復号検証
        cipher_ex1
            .decrypt_in_place_detached(&nonce_ex1, &[], &mut buf_ex4, &tag_ex4)
            .expect("RFC 8452 Example 4 復号に成功。");
        assert_eq!(
            buf_ex4, plaintext_ex4,
            "RFC 8452 Example 4 復号平文復元に成功。"
        );
    }

    #[test]
    fn test_xchacha20_poly1305_kat_vector() {
        // draft-arciszewski-xchacha-03 Test Vector (Appendix A.1)
        let key: [u8; KEY_LEN] = [
            0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d,
            0x8e, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
            0x9c, 0x9d, 0x9e, 0x9f,
        ];
        let nonce: [u8; XCHACHA20_POLY1305_NONCE_LEN] = [
            0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d,
            0x4e, 0x4f, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,
        ];
        let aad: [u8; 12] = [
            0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
        ];
        let plaintext = b"Ladies and Gentlemen of the class of '99: \
            If I could offer you only one tip for the future, sunscreen would be it.";

        let expected_ciphertext: [u8; 114] = [
            0xbd, 0x6d, 0x17, 0x9d, 0x3e, 0x83, 0xd4, 0x3b, 0x95, 0x76, 0x57, 0x94, 0x93, 0xc0,
            0xe9, 0x39, 0x57, 0x2a, 0x17, 0x00, 0x25, 0x2b, 0xfa, 0xcc, 0xbe, 0xd2, 0x90, 0x2c,
            0x21, 0x39, 0x6c, 0xbb, 0x73, 0x1c, 0x7f, 0x1b, 0x0b, 0x4a, 0xa6, 0x44, 0x0b, 0xf3,
            0xa8, 0x2f, 0x4e, 0xda, 0x7e, 0x39, 0xae, 0x64, 0xc6, 0x70, 0x8c, 0x54, 0xc2, 0x16,
            0xcb, 0x96, 0xb7, 0x2e, 0x12, 0x13, 0xb4, 0x52, 0x2f, 0x8c, 0x9b, 0xa4, 0x0d, 0xb5,
            0xd9, 0x45, 0xb1, 0x1b, 0x69, 0xb9, 0x82, 0xc1, 0xbb, 0x9e, 0x3f, 0x3f, 0xac, 0x2b,
            0xc3, 0x69, 0x48, 0x8f, 0x76, 0xb2, 0x38, 0x35, 0x65, 0xd3, 0xff, 0xf9, 0x21, 0xf9,
            0x66, 0x4c, 0x97, 0x63, 0x7d, 0xa9, 0x76, 0x88, 0x12, 0xf6, 0x15, 0xc6, 0x8b, 0x13,
            0xb5, 0x2e,
        ];
        let expected_tag: [u8; TAG_LEN] = [
            0xc0, 0x87, 0x59, 0x24, 0xc1, 0xc7, 0x98, 0x79, 0x47, 0xde, 0xaf, 0xd8, 0x78, 0x0a,
            0xcf, 0x49,
        ];

        let cipher = VaultCipher::new(CipherSuiteId::XChaCha20Poly1305, &key);
        let mut buf = *plaintext;
        let tag = cipher
            .encrypt_in_place_detached(&nonce, &aad, &mut buf)
            .expect("XChaCha20-Poly1305 KAT 暗号化に成功。");

        assert_eq!(
            buf, expected_ciphertext,
            "XChaCha20-Poly1305 公式KAT暗号文突合に成功。"
        );
        assert_eq!(
            tag, expected_tag,
            "XChaCha20-Poly1305 公式KAT認証タグ突合に成功。"
        );

        // 復号往復の確認
        cipher
            .decrypt_in_place_detached(&nonce, &aad, &mut buf, &tag)
            .expect("XChaCha20-Poly1305 KAT 復号に成功。");
        assert_eq!(
            buf.as_slice(),
            plaintext.as_slice(),
            "XChaCha20-Poly1305 KAT 平文完全一致の確認に成功。"
        );
    }

    #[test]
    fn test_validation_helpers_exhaustive() {
        // ノンス長検証
        assert_eq!(
            validate_nonce_len(
                CipherSuiteId::XChaCha20Poly1305,
                &[0u8; XCHACHA20_POLY1305_NONCE_LEN]
            ),
            Ok(()),
            "XChaCha20ノンス長24バイトの検証に成功。"
        );
        assert_eq!(
            validate_nonce_len(CipherSuiteId::XChaCha20Poly1305, &[0u8; 12]),
            Err(CryptoError::InvalidNonceSize),
            "XChaCha20短小ノンス拒絶に成功。"
        );
        assert_eq!(
            validate_nonce_len(
                CipherSuiteId::Aes256GcmSiv,
                &[0u8; AES_256_GCM_SIV_NONCE_LEN]
            ),
            Ok(()),
            "AES-GCM-SIVノンス長12バイトの検証に成功。"
        );
        assert_eq!(
            validate_nonce_len(CipherSuiteId::Aes256GcmSiv, &[0u8; 24]),
            Err(CryptoError::InvalidNonceSize),
            "AES-GCM-SIV長大ノンス拒絶に成功。"
        );

        // タグ長検証
        assert_eq!(
            validate_tag_len(&[0u8; TAG_LEN]),
            Ok(()),
            "タグ長16バイトの検証に成功。"
        );
        assert_eq!(
            validate_tag_len(&[]),
            Err(CryptoError::InvalidTagSize),
            "空タグの拒絶に成功。"
        );
        assert_eq!(
            validate_tag_len(&[0u8; 15]),
            Err(CryptoError::InvalidTagSize),
            "15バイトタグの拒絶に成功。"
        );
        assert_eq!(
            validate_tag_len(&[0u8; 17]),
            Err(CryptoError::InvalidTagSize),
            "17バイトタグの拒読に成功。"
        );

        // ペイロード長・AAD長検証
        assert_eq!(
            validate_payload_len(b"normal payload"),
            Ok(()),
            "通常ペイロード長検証に成功。"
        );
        assert_eq!(
            validate_payload_len(&[]),
            Ok(()),
            "空ペイロード長検証に成功。"
        );
        assert_eq!(
            validate_aad_len(b"normal aad"),
            Ok(()),
            "通常AAD長検証に成功。"
        );
    }

    #[test]
    fn test_payload_and_aad_max_len_constants() {
        #[cfg(target_pointer_width = "64")]
        {
            assert_eq!(
                MAX_PAYLOAD_LEN, 68_719_476_705,
                "64-bit環境におけるMAX_PAYLOAD_LEN値照合に成功。"
            );
            assert_eq!(
                MAX_AAD_LEN, 68_719_476_735,
                "64-bit環境におけるMAX_AAD_LEN値照合に成功。"
            );
        }
        #[cfg(not(target_pointer_width = "64"))]
        {
            assert_eq!(
                MAX_PAYLOAD_LEN,
                usize::MAX - TAG_LEN,
                "32-bit環境におけるMAX_PAYLOAD_LEN値照合に成功。"
            );
            assert_eq!(
                MAX_AAD_LEN,
                usize::MAX,
                "32-bit環境におけるMAX_AAD_LEN値照合に成功。"
            );
        }
    }

    #[test]
    fn test_pre_validation_and_zeroize_on_error() {
        let key = [0x55u8; KEY_LEN];
        let cipher_x = VaultCipher::new(CipherSuiteId::XChaCha20Poly1305, &key);
        let valid_nonce = [0x66u8; XCHACHA20_POLY1305_NONCE_LEN];
        let invalid_nonce = [0x66u8; 10];
        let aad = b"test-aad";

        // 1. encrypt_in_place_detached における不正ノンス時のエラー返却と平文バッファ保持(再試行可能)
        let original_plaintext = *b"Super Secret Plaintext Data Must Survive!";
        let mut sensitive_buf = original_plaintext;
        let res_enc_err =
            cipher_x.encrypt_in_place_detached(&invalid_nonce, aad, &mut sensitive_buf);
        assert_eq!(
            res_enc_err,
            Err(CryptoError::InvalidNonceSize),
            "不正ノンスによる暗号化拒絶に成功。"
        );
        assert_eq!(
            sensitive_buf, original_plaintext,
            "開始前の引数検証エラー時は呼び出し元平文バッファを破壊しないことを確認。"
        );
        // 正しいノンスでの再試行が成功することを確認。
        let retry_tag = cipher_x
            .encrypt_in_place_detached(&valid_nonce, aad, &mut sensitive_buf)
            .expect("正しいノンスでの再試行暗号化に成功。");
        cipher_x
            .decrypt_in_place_detached_tag(&valid_nonce, aad, &mut sensitive_buf, &retry_tag)
            .expect("再試行暗号文の復号に成功。");
        assert_eq!(
            sensitive_buf, original_plaintext,
            "再試行後の復号で元の平文を完全に復元。"
        );

        // 2. decrypt_in_place_detached における引数検証エラー時の暗号文バッファ保持(再試行可能)
        let plaintext = b"Fixed Array Tag Decryption Test";
        let mut roundtrip_buf = *plaintext;
        let valid_tag = cipher_x
            .encrypt_in_place_detached(&valid_nonce, aad, &mut roundtrip_buf)
            .expect("暗号化に成功。");

        let mut dec_retry_buf = roundtrip_buf;
        let invalid_tag = [0xbbu8; 15];
        let res_dec_tag_err =
            cipher_x.decrypt_in_place_detached(&valid_nonce, aad, &mut dec_retry_buf, &invalid_tag);
        assert_eq!(
            res_dec_tag_err,
            Err(CryptoError::InvalidTagSize),
            "不正タグ長による復号拒絶に成功。"
        );
        assert_eq!(
            dec_retry_buf, roundtrip_buf,
            "不正タグ長検出時は呼び出し元暗号文バッファを破壊しないことを確認。"
        );

        let res_dec_nonce_err =
            cipher_x.decrypt_in_place_detached(&invalid_nonce, aad, &mut dec_retry_buf, &valid_tag);
        assert_eq!(
            res_dec_nonce_err,
            Err(CryptoError::InvalidNonceSize),
            "不正ノンス長による復号拒絶に成功。"
        );
        assert_eq!(
            dec_retry_buf, roundtrip_buf,
            "不正ノンス長検出時は呼び出し元暗号文バッファを破壊しないことを確認。"
        );

        // 引数修正後の再試行復号が成功することを確認。
        cipher_x
            .decrypt_in_place_detached(&valid_nonce, aad, &mut dec_retry_buf, &valid_tag)
            .expect("正しい引数での再試行復号に成功。");
        assert_eq!(
            dec_retry_buf.as_slice(),
            plaintext.as_slice(),
            "再試行後の復号で元の平文を完全に復元。"
        );

        // 3. decrypt_in_place_detached_tag (固定長配列タグ) の正常系、再試行、および改ざん検知
        // 正常復号
        let mut dec_buf = roundtrip_buf;
        cipher_x
            .decrypt_in_place_detached_tag(&valid_nonce, aad, &mut dec_buf, &valid_tag)
            .expect("固定長タグ配列による復号に成功。");
        assert_eq!(
            dec_buf.as_slice(),
            plaintext.as_slice(),
            "固定長タグ配列による平文復元に成功。"
        );

        // 不正ノンス長での遮断と暗号文バッファ保持(再試行可能)
        let mut bad_nonce_dec_buf = roundtrip_buf;
        let res_bad_nonce = cipher_x.decrypt_in_place_detached_tag(
            &invalid_nonce,
            aad,
            &mut bad_nonce_dec_buf,
            &valid_tag,
        );
        assert_eq!(
            res_bad_nonce,
            Err(CryptoError::InvalidNonceSize),
            "固定長タグ経路の不正ノンス拒絶に成功。"
        );
        assert_eq!(
            bad_nonce_dec_buf, roundtrip_buf,
            "固定長タグ経路の不正ノンス検出時は暗号文バッファを破壊しないことを確認。"
        );
        cipher_x
            .decrypt_in_place_detached_tag(&valid_nonce, aad, &mut bad_nonce_dec_buf, &valid_tag)
            .expect("固定長タグ経路の再試行復号に成功。");
        assert_eq!(
            bad_nonce_dec_buf.as_slice(),
            plaintext.as_slice(),
            "固定長タグ経路の再試行復号で元の平文を完全に復元。"
        );

        // AES-256-GCM-SIV でも同様に事前検証エラー時に暗号文バッファが保持されることを確認。
        let cipher_aes = VaultCipher::new(CipherSuiteId::Aes256GcmSiv, &key);
        let valid_aes_nonce = [0x77u8; AES_256_GCM_SIV_NONCE_LEN];
        let invalid_aes_nonce = [0x77u8; XCHACHA20_POLY1305_NONCE_LEN];
        let mut aes_ct_buf = *plaintext;
        let aes_tag = cipher_aes
            .encrypt_in_place_detached(&valid_aes_nonce, aad, &mut aes_ct_buf)
            .expect("AES-256-GCM-SIV 暗号化に成功。");
        let mut aes_dec_buf = aes_ct_buf;
        assert_eq!(
            cipher_aes.decrypt_in_place_detached_tag(
                &invalid_aes_nonce,
                aad,
                &mut aes_dec_buf,
                &aes_tag
            ),
            Err(CryptoError::InvalidNonceSize),
            "AES-256-GCM-SIV 固定長タグ経路の不正ノンス拒絶に成功。"
        );
        assert_eq!(
            aes_dec_buf, aes_ct_buf,
            "AES-256-GCM-SIV 不正ノンス検出時は暗号文バッファを破壊しないことを確認。"
        );
        cipher_aes
            .decrypt_in_place_detached_tag(&valid_aes_nonce, aad, &mut aes_dec_buf, &aes_tag)
            .expect("AES-256-GCM-SIV 再試行復号に成功。");
        assert_eq!(
            aes_dec_buf.as_slice(),
            plaintext.as_slice(),
            "AES-256-GCM-SIV 再試行復号で元の平文を完全に復元。"
        );

        // 改ざんタグでの遮断とゼロクリア
        let mut tampered_tag = valid_tag;
        tampered_tag[0] ^= 0xff;
        let mut tampered_dec_buf = roundtrip_buf;
        let res_tampered = cipher_x.decrypt_in_place_detached_tag(
            &valid_nonce,
            aad,
            &mut tampered_dec_buf,
            &tampered_tag,
        );
        assert_eq!(
            res_tampered,
            Err(CryptoError::AeadDecryptionFailed),
            "改ざん固定長タグの遮断に成功。"
        );
        assert_eq!(
            tampered_dec_buf, [0u8; 31],
            "固定長タグ改ざん検出時の揮発ゼロクリアに成功。"
        );

        // 4. 空平文(0バイト)のパニックフリー暗号化・復号
        let mut empty_buf: [u8; 0] = [];
        let empty_tag = cipher_x
            .encrypt_in_place_detached(&valid_nonce, aad, &mut empty_buf)
            .expect("空平文の暗号化に成功。");
        cipher_x
            .decrypt_in_place_detached_tag(&valid_nonce, aad, &mut empty_buf, &empty_tag)
            .expect("空平文の復号に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_alloc_boundary_slice_validation() {
        let key = [0x88u8; KEY_LEN];
        let cipher_aes = VaultCipher::new(CipherSuiteId::Aes256GcmSiv, &key);
        let nonce = [0x99u8; AES_256_GCM_SIV_NONCE_LEN];
        let aad = b"alloc-boundary-test";

        // 空暗号文およびタグ長未満(0〜15バイト)の decrypt に対するトラップフリー性検証
        for len in 0..TAG_LEN {
            let short_data = alloc::vec![0xcc; len];
            let res = cipher_aes.decrypt(&nonce, &short_data, aad);
            assert_eq!(
                res.err(),
                Some(CryptoError::InvalidTagSize),
                "タグ長未満データのパニックフリー遮断に成功。"
            );
        }

        // 不正ノンス長の decrypt に対する遮断
        let invalid_nonce = [0x99u8; 24];
        let dummy_ct = alloc::vec![0xdd; TAG_LEN + 10];
        assert_eq!(
            cipher_aes.decrypt(&invalid_nonce, &dummy_ct, aad).err(),
            Some(CryptoError::InvalidNonceSize),
            "不正ノンス長での復号拒絶に成功。"
        );
        assert_eq!(
            cipher_aes.encrypt(&invalid_nonce, b"hello", aad),
            Err(CryptoError::InvalidNonceSize),
            "AES-GCM-SIV 不正ノンス長での暗号化拒絶に成功。"
        );
        let cipher_x = VaultCipher::new(CipherSuiteId::XChaCha20Poly1305, &key);
        let invalid_x_nonce = [0x99u8; AES_256_GCM_SIV_NONCE_LEN];
        assert_eq!(
            cipher_x.encrypt(&invalid_x_nonce, b"hello", aad),
            Err(CryptoError::InvalidNonceSize),
            "XChaCha20-Poly1305 不正ノンス長での暗号化拒絶に成功。"
        );

        // 空平文の alloc 暗号化・復号
        let ct_empty = cipher_aes
            .encrypt(&nonce, &[], aad)
            .expect("空平文暗号化に成功。");
        assert_eq!(ct_empty.len(), TAG_LEN, "空平文暗号文長はタグ長と一致。");
        let pt_empty = cipher_aes
            .decrypt(&nonce, &ct_empty, aad)
            .expect("空平文復号に成功。");
        assert!(pt_empty.is_empty(), "復号された平文が空であることを確認。");
    }

    #[test]
    fn test_vault_cipher_zeroize_on_drop() {
        fn assert_zeroize_on_drop<T: zeroize::ZeroizeOnDrop>(_val: &T) {}

        assert!(
            core::mem::needs_drop::<VaultCipher>(),
            "VaultCipher が Drop 対象であることを確認。"
        );
        assert!(
            core::mem::needs_drop::<XChaCha20Poly1305>(),
            "XChaCha20Poly1305 が Drop 対象であることを確認。"
        );
        assert!(
            core::mem::needs_drop::<aes::Aes256>(),
            "aes::Aes256(zeroize有効)が Drop 対象であることを確認。"
        );

        let key = [0x42u8; KEY_LEN];
        let cipher_x = VaultCipher::new(CipherSuiteId::XChaCha20Poly1305, &key);
        assert_zeroize_on_drop(&cipher_x);
        drop(cipher_x);

        let cipher_aes = VaultCipher::new(CipherSuiteId::Aes256GcmSiv, &key);
        assert_zeroize_on_drop(&cipher_aes);
        drop(cipher_aes);
    }
}
