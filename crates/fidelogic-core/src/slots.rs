//! # マルチスロット暗号化ラップ・復号パイプラインモジュール。
//!
//! エンベロープ暗号化における各 KEK スロットのバイナリフォーマット定義,
//! 鍵導出(KDF), XChaCha20-Poly1305 を用いた DEK (256-bit) の
//! ラップ(暗号化)およびアンラップ(復号)パイプラインを提供する。
//!
//! ## Slot 0 (Argon2id マスターパスワード) フォーマット
//! [`KekSlotEntry::wrapped_dek`] には以下の固定長 100 バイト構造を格納する。
//! - `m_cost`: 4 バイト (ビッグエンディアン `u32`, KiB単位)。
//! - `t_cost`: 4 バイト (ビッグエンディアン `u32`, 反復回数)。
//! - `p_cost`: 4 バイト (ビッグエンディアン `u32`, 並列度)。
//! - `salt`: 16 バイト (Argon2id ソルト)。
//! - `nonce`: 24 バイト (XChaCha20-Poly1305 192-bit ノンス)。
//! - `ciphertext`: 32 バイト (暗号化済み 256-bit DEK)。
//! - `auth_tag`: 16 バイト (Poly1305 認証タグ)。
//!
//! ## Slot 1 (WebAuthn PRF / HKDF-SHA256) および Slot 2 (リカバリーコード) フォーマット
//!
//! [`KekSlotEntry::wrapped_dek`] には以下の固定長 104 バイト構造を格納する。
//! - `salt`: 32 バイト (HKDF-SHA256 ソルト)。
//! - `nonce`: 24 バイト (XChaCha20-Poly1305 192-bit ノンス)。
//! - `ciphertext`: 32 バイト (暗号化済み 256-bit DEK)。
//! - `auth_tag`: 16 バイト (Poly1305 認証タグ)。

use crate::cipher::{
    CipherSuiteId, MAX_AAD_LEN, TAG_LEN, VaultCipher, XCHACHA20_POLY1305_NONCE_LEN,
};
use crate::envelope::{
    DEK_LEN, KekSlots, SLOT_ID_ARGON2ID, SLOT_ID_PRF, SLOT_ID_RECOVERY, SlotKind, SlotStatus,
    VaultEngine,
};
use crate::error::{CryptoError, TlvParseError, VaultError};
use crate::kdf::{Argon2Params, hkdf_sha256_derive_32};
use crate::tlv::{KekSlotEntry, VAULT_HEADER_LEN, Vault, VaultHeader};
use crate::zeroize::{SecretBytes, SecretVec, volatile_zeroize};

/// Slot 0 (Argon2id マスターパスワード) の KDF 種別識別子。
pub const KDF_KIND_ARGON2ID: u8 = 1;

/// Slot 1 (HKDF-SHA256 / WebAuthn PRF) の KDF 種別識別子。
pub const KDF_KIND_HKDF_SHA256: u8 = 2;

/// Slot 2 (高エントロピーリカバリーコード) の KDF 種別識別子。
pub const KDF_KIND_RECOVERY: u8 = 3;

/// スロットの DEK ラップおよび復号に使用する AEAD 暗号スイート (XChaCha20-Poly1305)。
pub const SLOT_CIPHER_SUITE: CipherSuiteId = CipherSuiteId::XChaCha20Poly1305;

/// Slot 0 (Argon2id) におけるソルト長 (16バイト = 128ビット)。
pub const SLOT0_SALT_LEN: usize = 16;

/// Slot 0 (Argon2id) における KDF パラメータヘッダー長 (`m_cost` + `t_cost` + `p_cost` = 12バイト)。
pub const SLOT0_PARAMS_LEN: usize = 12;

/// Slot 0 (Argon2id) におけるノンス長 (XChaCha20-Poly1305 192-bit = 24バイト)。
pub const SLOT0_NONCE_LEN: usize = XCHACHA20_POLY1305_NONCE_LEN;

/// Slot 0 (Argon2id) における暗号化済み DEK 本体のバイト長 (256-bit = 32バイト)。
pub const SLOT0_CIPHERTEXT_LEN: usize = DEK_LEN;

/// Slot 0 (Argon2id) における認証タグ長 (128-bit = 16バイト)。
pub const SLOT0_TAG_LEN: usize = TAG_LEN;

/// Slot 0 (Argon2id) の `wrapped_dek` フィールド総バイト長 (100バイト)。
pub const SLOT0_WRAPPED_DEK_LEN: usize =
    SLOT0_PARAMS_LEN + SLOT0_SALT_LEN + SLOT0_NONCE_LEN + SLOT0_CIPHERTEXT_LEN + SLOT0_TAG_LEN;

/// Slot 0 デコード時に許容する Argon2id メモリコスト安全上限 (KiB単位: 1 GiB)。
///
/// 不正な Vault データによる Wasm 環境やネイティブ環境でのメモリ枯渇(OOM)を防止する。
pub const MAX_SLOT0_M_COST: u32 = 1_048_576;

/// Slot 0 デコード時に許容する Argon2id 時間コスト安全上限。
pub const MAX_SLOT0_T_COST: u32 = 1_024;

/// Slot 0 デコード時に許容する Argon2id 並列度安全上限。
pub const MAX_SLOT0_P_COST: u32 = 64;

/// Slot 0 の AEAD 関連データ (AAD) に付与するドメイン分離プレフィックス。
const SLOT0_AAD_PREFIX: &[u8; 18] = b"fidelogic-slot0-v1";

/// Slot 0 固定 AAD ヘッダー部の総バイト長 (48バイト)。
///
/// [`SLOT0_AAD_PREFIX`] (18B) + `slot_id` (1B) + `kdf_kind` (1B) + `params` (12B) + `salt` (16B) で構成される。
const SLOT0_AAD_FIXED_LEN: usize = 18 + 2 + SLOT0_PARAMS_LEN + SLOT0_SALT_LEN;

/// Slot 1 (WebAuthn PRF / HKDF-SHA256) におけるソルト長 (32バイト = 256ビット)。
pub const SLOT1_SALT_LEN: usize = 32;

/// Slot 1 (WebAuthn PRF) におけるノンス長 (XChaCha20-Poly1305 192-bit = 24バイト)。
pub const SLOT1_NONCE_LEN: usize = XCHACHA20_POLY1305_NONCE_LEN;

/// Slot 1 (WebAuthn PRF) における暗号化済み DEK 本体のバイト長 (256-bit = 32バイト)。
pub const SLOT1_CIPHERTEXT_LEN: usize = DEK_LEN;

/// Slot 1 (WebAuthn PRF) における認証タグ長 (128-bit = 16バイト)。
pub const SLOT1_TAG_LEN: usize = TAG_LEN;

/// Slot 1 (WebAuthn PRF) の `wrapped_dek` フィールド総バイト長 (104バイト)。
pub const SLOT1_WRAPPED_DEK_LEN: usize =
    SLOT1_SALT_LEN + SLOT1_NONCE_LEN + SLOT1_CIPHERTEXT_LEN + SLOT1_TAG_LEN;

/// Slot 1 (WebAuthn PRF) で要求する最小 PRF シークレット長 (32バイト = 256ビット)。
pub const SLOT1_MIN_PRF_LEN: usize = 32;

/// Slot 2 (高エントロピーリカバリーコード) におけるソルト長 (32バイト = 256ビット)。
pub const SLOT2_SALT_LEN: usize = 32;

/// Slot 2 (リカバリーコード) におけるノンス長 (XChaCha20-Poly1305 192-bit = 24バイト)。
pub const SLOT2_NONCE_LEN: usize = XCHACHA20_POLY1305_NONCE_LEN;

/// Slot 2 (リカバリーコード) における暗号化済み DEK 本体のバイト長 (256-bit = 32バイト)。
pub const SLOT2_CIPHERTEXT_LEN: usize = DEK_LEN;

/// Slot 2 (リカバリーコード) における認証タグ長 (128-bit = 16バイト)。
pub const SLOT2_TAG_LEN: usize = TAG_LEN;

/// Slot 2 (リカバリーコード) の `wrapped_dek` フィールド総バイト長 (104バイト)。
pub const SLOT2_WRAPPED_DEK_LEN: usize =
    SLOT2_SALT_LEN + SLOT2_NONCE_LEN + SLOT2_CIPHERTEXT_LEN + SLOT2_TAG_LEN;

/// Slot 2 で要求する最小生リカバリーシークレット長 (16バイト = 128ビット)。
pub const SLOT2_MIN_SECRET_LEN: usize = 16;

/// Slot 2 の整形済み英数字リカバリーコードについて、正準化後に要求する最小文字数 (24文字)。
pub const SLOT2_MIN_CODE_LEN: usize = 24;

/// 整形済みリカバリーコード入力の許容最大バイト長 (512バイト)。
const MAX_RECOVERY_CODE_INPUT_LEN: usize = 512;

/// タイミング平滑化用ダミー演算で使用する固定ダミーパスワード (Slot 0)。
const DUMMY_SLOT0_PASSWORD: &[u8; 27] = b"fidelogic-dummy-password-v1";

/// タイミング平滑化用ダミー演算で使用する固定ダミーソルト (Slot 0)。
const DUMMY_SLOT0_SALT: [u8; SLOT0_SALT_LEN] = [0xA5; SLOT0_SALT_LEN];

/// タイミング平滑化用ダミー演算で使用する固定ダミーソルト (Slot 1 / Slot 2)。
const DUMMY_HKDF_SALT: [u8; SLOT1_SALT_LEN] = [0x55; SLOT1_SALT_LEN];

/// タイミング平滑化用ダミー演算で使用する固定ダミー入力鍵素材 (Slot 1 / Slot 2)。
const DUMMY_HKDF_IKM: [u8; SLOT1_MIN_PRF_LEN] = [0x66; SLOT1_MIN_PRF_LEN];

/// タイミング平滑化用ダミー演算で使用する固定ダミーリカバリーコード (Slot 2)。
const DUMMY_RECOVERY_CODE: &[u8; 34] = b"DUMM-YREC-OVER-YCOD-E000-0000-0000";

/// タイミング平滑化用ダミー AEAD 復号で使用する固定ダミーノンス。
const DUMMY_NONCE: [u8; XCHACHA20_POLY1305_NONCE_LEN] = [0x5A; XCHACHA20_POLY1305_NONCE_LEN];

/// タイミング平滑化用ダミー AEAD 復号で使用する固定ダミー暗号文。
const DUMMY_CIPHERTEXT: [u8; DEK_LEN] = [0x3C; DEK_LEN];

/// タイミング平滑化用ダミー AEAD 復号で使用する固定ダミー認証タグ。
const DUMMY_TAG: [u8; TAG_LEN] = [0xC3; TAG_LEN];

/// タイミング平滑化用ダミー AEAD 復号フォールバックで使用するダミー KEK シード。
const DUMMY_KEK_SEED: [u8; DEK_LEN] = [0x7E; DEK_LEN];

/// Slot 1 の AEAD 関連データ (AAD) に付与するドメイン分離プレフィックス。
const SLOT1_AAD_PREFIX: &[u8; 18] = b"fidelogic-slot1-v1";

/// Slot 1 の HKDF-SHA256 展開時に使用するドメイン分離コンテキスト文字列。
const SLOT1_HKDF_INFO: &[u8] = b"fidelogic-slot1-hkdf-sha256-kek-v1";

/// Slot 2 の AEAD 関連データ (AAD) に付与するドメイン分離プレフィックス。
const SLOT2_AAD_PREFIX: &[u8; 18] = b"fidelogic-slot2-v1";

/// Slot 2 の HKDF-SHA256 展開時に使用するドメイン分離コンテキスト文字列。
const SLOT2_HKDF_INFO: &[u8] = b"fidelogic-slot2-recovery-hkdf-sha256-kek-v1";

/// Slot 1 および Slot 2 に共通する HKDF スロット固定 AAD ヘッダー長 (52バイト)。
///
/// AAD プレフィックス (18B) + `slot_id` (1B) + `kdf_kind` (1B) + `salt` (32B) で構成される。
const HKDF_SLOT_AAD_FIXED_LEN: usize = 18 + 2 + SLOT1_SALT_LEN;

/// KEK スロットで使用される鍵導出方式の種別を表す列挙型。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum KdfKind {
    /// Slot 0: Argon2id パスワード鍵導出。
    Argon2id = KDF_KIND_ARGON2ID,
    /// Slot 1: HKDF-SHA256 (WebAuthn PRF 等)。
    HkdfSha256 = KDF_KIND_HKDF_SHA256,
    /// Slot 2: 高エントロピーリカバリーコード鍵導出。
    Recovery = KDF_KIND_RECOVERY,
}

impl KdfKind {
    /// 数値識別子から [`KdfKind`] への変換を試みる。
    ///
    /// # Errors
    ///
    /// 未知の識別子が指定された場合は [`TlvParseError::UnsupportedSuite`] を返す。
    #[inline]
    pub const fn from_u8(value: u8) -> Result<Self, TlvParseError> {
        match value {
            KDF_KIND_ARGON2ID => Ok(Self::Argon2id),
            KDF_KIND_HKDF_SHA256 => Ok(Self::HkdfSha256),
            KDF_KIND_RECOVERY => Ok(Self::Recovery),
            _ => Err(TlvParseError::UnsupportedSuite),
        }
    }

    /// 対応する数値識別子を返す。
    #[inline]
    #[must_use]
    pub const fn as_u8(self) -> u8 {
        self as u8
    }
}

impl TryFrom<u8> for KdfKind {
    type Error = TlvParseError;

    #[inline]
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::from_u8(value)
    }
}

impl From<KdfKind> for u8 {
    #[inline]
    fn from(kind: KdfKind) -> Self {
        kind.as_u8()
    }
}

/// Slot 0 (Argon2id マスターパスワード) の暗号化 DEK ペイロード構造体。
///
/// KDF パラメータ, ソルト, 192-bit ノンス, 暗号化 DEK 本体, 認証タグを保持する。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Argon2idSlotPayload {
    /// 復号時に使用する Argon2id パラメータ (`output_len == 32` 固定)。
    pub params: Argon2Params,
    /// Argon2id ソルト (16バイト)。
    pub salt: [u8; SLOT0_SALT_LEN],
    /// XChaCha20-Poly1305 ノンス (24バイト)。
    pub nonce: [u8; SLOT0_NONCE_LEN],
    /// 暗号化された 256-bit DEK 本体 (32バイト)。
    pub ciphertext: [u8; SLOT0_CIPHERTEXT_LEN],
    /// Poly1305 認証タグ (16バイト)。
    pub auth_tag: [u8; SLOT0_TAG_LEN],
}

impl Argon2idSlotPayload {
    /// 固定長 100 バイトのバイナリ表現から [`Argon2idSlotPayload`] をデコードおよび検証する。
    ///
    /// # Errors
    ///
    /// - 入力長が [`SLOT0_WRAPPED_DEK_LEN`] と一致しない場合は [`VaultError::Parse`] ([`TlvParseError::InvalidLength`]) を返す。
    /// - Argon2id パラメータが RFC 9106 制約または安全上限を満たさない場合は [`VaultError::Crypto`] ([`CryptoError::InvalidParameter`]) を返す。
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, VaultError> {
        if bytes.len() != SLOT0_WRAPPED_DEK_LEN {
            return Err(VaultError::Parse(TlvParseError::InvalidLength));
        }

        let (m_cost_bytes, rest) = bytes
            .split_first_chunk::<4>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;
        let (t_cost_bytes, rest) = rest
            .split_first_chunk::<4>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;
        let (p_cost_bytes, rest) = rest
            .split_first_chunk::<4>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;

        let m_cost = u32::from_be_bytes(*m_cost_bytes);
        let t_cost = u32::from_be_bytes(*t_cost_bytes);
        let p_cost = u32::from_be_bytes(*p_cost_bytes);

        let params = Argon2Params::custom(m_cost, t_cost, p_cost, Some(DEK_LEN))?;
        validate_slot0_argon2_params(&params)?;

        let (salt, rest) = rest
            .split_first_chunk::<SLOT0_SALT_LEN>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;
        let (nonce, rest) = rest
            .split_first_chunk::<SLOT0_NONCE_LEN>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;
        let (ciphertext, rest) = rest
            .split_first_chunk::<SLOT0_CIPHERTEXT_LEN>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;
        let (auth_tag, rest) = rest
            .split_first_chunk::<SLOT0_TAG_LEN>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;

        if !rest.is_empty() {
            return Err(VaultError::Parse(TlvParseError::InvalidLength));
        }

        Ok(Self {
            params,
            salt: *salt,
            nonce: *nonce,
            ciphertext: *ciphertext,
            auth_tag: *auth_tag,
        })
    }

    /// 構造体を固定長 100 バイトのバイナリ表現へシリアライズする。
    #[must_use]
    pub fn to_bytes(&self) -> [u8; SLOT0_WRAPPED_DEK_LEN] {
        let mut out = [0u8; SLOT0_WRAPPED_DEK_LEN];
        out[0..4].copy_from_slice(&self.params.m_cost().to_be_bytes());
        out[4..8].copy_from_slice(&self.params.t_cost().to_be_bytes());
        out[8..12].copy_from_slice(&self.params.p_cost().to_be_bytes());
        out[12..28].copy_from_slice(&self.salt);
        out[28..52].copy_from_slice(&self.nonce);
        out[52..84].copy_from_slice(&self.ciphertext);
        out[84..100].copy_from_slice(&self.auth_tag);
        out
    }

    /// TLV の [`KekSlotEntry`] が有効な Slot 0 エントリであるかを検証し、ペイロードを抽出する。
    ///
    /// # Errors
    ///
    /// - `slot_id != SLOT_ID_ARGON2ID` または `kdf_kind != KDF_KIND_ARGON2ID` の場合は
    ///   [`VaultError::Parse`] ([`TlvParseError::InvalidFormat`]) を返す。
    /// - 内部ペイロード長や Argon2id パラメータが不正な場合は対応する [`VaultError`] を返す。
    pub fn from_slot_entry(entry: &KekSlotEntry) -> Result<Self, VaultError> {
        if entry.slot_id() != SLOT_ID_ARGON2ID || entry.kdf_kind() != KDF_KIND_ARGON2ID {
            return Err(VaultError::Parse(TlvParseError::InvalidFormat));
        }
        Self::from_bytes(entry.wrapped_dek())
    }

    /// TLV の [`KekSlotEntry`] へ変換する。
    ///
    /// # Errors
    ///
    /// スロットエントリ長制限を超過する場合は [`VaultError::Parse`] を返す。
    pub fn to_slot_entry(&self) -> Result<KekSlotEntry, VaultError> {
        let bytes = self.to_bytes();
        KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, bytes.to_vec())
            .map_err(VaultError::from)
    }
}

/// Slot 1 および Slot 2 で共有される固定長 104 バイト HKDF スロットの内部表現。
#[derive(Debug, Clone, PartialEq, Eq)]
struct HkdfSlotFields {
    salt: [u8; SLOT1_SALT_LEN],
    nonce: [u8; SLOT1_NONCE_LEN],
    ciphertext: [u8; SLOT1_CIPHERTEXT_LEN],
    auth_tag: [u8; SLOT1_TAG_LEN],
}

impl HkdfSlotFields {
    fn from_bytes(bytes: &[u8]) -> Result<Self, VaultError> {
        if bytes.len() != SLOT1_WRAPPED_DEK_LEN {
            return Err(VaultError::Parse(TlvParseError::InvalidLength));
        }

        let (salt, rest) = bytes
            .split_first_chunk::<SLOT1_SALT_LEN>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;
        let (nonce, rest) = rest
            .split_first_chunk::<SLOT1_NONCE_LEN>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;
        let (ciphertext, rest) = rest
            .split_first_chunk::<SLOT1_CIPHERTEXT_LEN>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;
        let (auth_tag, rest) = rest
            .split_first_chunk::<SLOT1_TAG_LEN>()
            .ok_or(VaultError::Parse(TlvParseError::InvalidLength))?;

        if !rest.is_empty() {
            return Err(VaultError::Parse(TlvParseError::InvalidLength));
        }

        Ok(Self {
            salt: *salt,
            nonce: *nonce,
            ciphertext: *ciphertext,
            auth_tag: *auth_tag,
        })
    }

    fn to_bytes(&self) -> [u8; SLOT1_WRAPPED_DEK_LEN] {
        let mut out = [0u8; SLOT1_WRAPPED_DEK_LEN];
        out[0..32].copy_from_slice(&self.salt);
        out[32..56].copy_from_slice(&self.nonce);
        out[56..88].copy_from_slice(&self.ciphertext);
        out[88..104].copy_from_slice(&self.auth_tag);
        out
    }

    fn from_slot_entry(entry: &KekSlotEntry, spec: &HkdfSlotSpec) -> Result<Self, VaultError> {
        if entry.slot_id() != spec.slot_id || entry.kdf_kind() != spec.kdf_kind {
            return Err(VaultError::Parse(TlvParseError::InvalidFormat));
        }
        Self::from_bytes(entry.wrapped_dek())
    }

    fn to_slot_entry(&self, spec: &HkdfSlotSpec) -> Result<KekSlotEntry, VaultError> {
        let bytes = self.to_bytes();
        KekSlotEntry::new(spec.slot_id, spec.kdf_kind, bytes.to_vec()).map_err(VaultError::from)
    }
}

/// Slot 1 および Slot 2 のドメイン分離パラメータを集約する内部仕様構造体。
#[derive(Clone, Copy)]
struct HkdfSlotSpec {
    slot_id: u8,
    kdf_kind: u8,
    aad_prefix: &'static [u8; 18],
    hkdf_info: &'static [u8],
    min_secret_len: usize,
}

const SLOT1_SPEC: HkdfSlotSpec = HkdfSlotSpec {
    slot_id: SLOT_ID_PRF,
    kdf_kind: KDF_KIND_HKDF_SHA256,
    aad_prefix: SLOT1_AAD_PREFIX,
    hkdf_info: SLOT1_HKDF_INFO,
    min_secret_len: SLOT1_MIN_PRF_LEN,
};

const SLOT2_SPEC: HkdfSlotSpec = HkdfSlotSpec {
    slot_id: SLOT_ID_RECOVERY,
    kdf_kind: KDF_KIND_RECOVERY,
    aad_prefix: SLOT2_AAD_PREFIX,
    hkdf_info: SLOT2_HKDF_INFO,
    min_secret_len: SLOT2_MIN_SECRET_LEN,
};

/// Slot 1 (WebAuthn PRF / HKDF-SHA256) の暗号化 DEK ペイロード構造体。
///
/// HKDF-SHA256 ソルト (32バイト), 192-bit ノンス (24バイト), 暗号化 DEK 本体 (32バイト), Poly1305 認証タグ (16バイト) の計 104 バイトを保持する。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrfSlotPayload {
    /// HKDF-SHA256 ソルト (32バイト)。
    pub salt: [u8; SLOT1_SALT_LEN],
    /// XChaCha20-Poly1305 ノンス (24バイト)。
    pub nonce: [u8; SLOT1_NONCE_LEN],
    /// 暗号化された 256-bit DEK 本体 (32バイト)。
    pub ciphertext: [u8; SLOT1_CIPHERTEXT_LEN],
    /// Poly1305 認証タグ (16バイト)。
    pub auth_tag: [u8; SLOT1_TAG_LEN],
}

impl PrfSlotPayload {
    fn as_fields(&self) -> HkdfSlotFields {
        HkdfSlotFields {
            salt: self.salt,
            nonce: self.nonce,
            ciphertext: self.ciphertext,
            auth_tag: self.auth_tag,
        }
    }

    fn from_fields(fields: HkdfSlotFields) -> Self {
        Self {
            salt: fields.salt,
            nonce: fields.nonce,
            ciphertext: fields.ciphertext,
            auth_tag: fields.auth_tag,
        }
    }

    /// 固定長 104 バイトのバイナリ表現から [`PrfSlotPayload`] をデコードする。
    ///
    /// # Errors
    ///
    /// 入力長が [`SLOT1_WRAPPED_DEK_LEN`] と一致しない場合は、
    /// [`VaultError::Parse`] ([`TlvParseError::InvalidLength`]) を返す。
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, VaultError> {
        HkdfSlotFields::from_bytes(bytes).map(Self::from_fields)
    }

    /// 構造体を固定長 104 バイトのバイナリ表現へシリアライズする。
    #[must_use]
    pub fn to_bytes(&self) -> [u8; SLOT1_WRAPPED_DEK_LEN] {
        self.as_fields().to_bytes()
    }

    /// TLV の [`KekSlotEntry`] が有効な Slot 1 エントリであるかを検証し、ペイロードを抽出する。
    ///
    /// # Errors
    ///
    /// - `slot_id != SLOT_ID_PRF` または `kdf_kind != KDF_KIND_HKDF_SHA256` の場合は、
    ///   [`VaultError::Parse`] ([`TlvParseError::InvalidFormat`]) を返す。
    /// - ペイロード長が不正な場合は [`VaultError::Parse`] ([`TlvParseError::InvalidLength`]) を返す。
    pub fn from_slot_entry(entry: &KekSlotEntry) -> Result<Self, VaultError> {
        HkdfSlotFields::from_slot_entry(entry, &SLOT1_SPEC).map(Self::from_fields)
    }

    /// TLV の [`KekSlotEntry`] へ変換する。
    ///
    /// # Errors
    ///
    /// スロットエントリ長制限を超過する場合は [`VaultError::Parse`] を返す。
    pub fn to_slot_entry(&self) -> Result<KekSlotEntry, VaultError> {
        self.as_fields().to_slot_entry(&SLOT1_SPEC)
    }
}

/// Slot 2 (高エントロピーリカバリーコード) の暗号化 DEK ペイロード構造体。
///
/// HKDF-SHA256 ソルト (32バイト), 192-bit ノンス (24バイト), 暗号化 DEK 本体 (32バイト), Poly1305 認証タグ (16バイト) の計 104 バイトを保持する。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoverySlotPayload {
    /// HKDF-SHA256 ソルト (32バイト)。
    pub salt: [u8; SLOT2_SALT_LEN],
    /// XChaCha20-Poly1305 ノンス (24バイト)。
    pub nonce: [u8; SLOT2_NONCE_LEN],
    /// 暗号化された 256-bit DEK 本体 (32バイト)。
    pub ciphertext: [u8; SLOT2_CIPHERTEXT_LEN],
    /// Poly1305 認証タグ (16バイト)。
    pub auth_tag: [u8; SLOT2_TAG_LEN],
}

impl RecoverySlotPayload {
    fn as_fields(&self) -> HkdfSlotFields {
        HkdfSlotFields {
            salt: self.salt,
            nonce: self.nonce,
            ciphertext: self.ciphertext,
            auth_tag: self.auth_tag,
        }
    }

    fn from_fields(fields: HkdfSlotFields) -> Self {
        Self {
            salt: fields.salt,
            nonce: fields.nonce,
            ciphertext: fields.ciphertext,
            auth_tag: fields.auth_tag,
        }
    }

    /// 固定長 104 バイトのバイナリ表現から [`RecoverySlotPayload`] をデコードする。
    ///
    /// # Errors
    ///
    /// 入力長が [`SLOT2_WRAPPED_DEK_LEN`] と一致しない場合は、
    /// [`VaultError::Parse`] ([`TlvParseError::InvalidLength`]) を返す。
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, VaultError> {
        HkdfSlotFields::from_bytes(bytes).map(Self::from_fields)
    }

    /// 構造体を固定長 104 バイトのバイナリ表現へシリアライズする。
    #[must_use]
    pub fn to_bytes(&self) -> [u8; SLOT2_WRAPPED_DEK_LEN] {
        self.as_fields().to_bytes()
    }

    /// TLV の [`KekSlotEntry`] が有効な Slot 2 エントリであるかを検証し、ペイロードを抽出する。
    ///
    /// # Errors
    ///
    /// - `slot_id != SLOT_ID_RECOVERY` または `kdf_kind != KDF_KIND_RECOVERY` の場合は、
    ///   [`VaultError::Parse`] ([`TlvParseError::InvalidFormat`]) を返す。
    /// - ペイロード長が不正な場合は [`VaultError::Parse`] ([`TlvParseError::InvalidLength`]) を返す。
    pub fn from_slot_entry(entry: &KekSlotEntry) -> Result<Self, VaultError> {
        HkdfSlotFields::from_slot_entry(entry, &SLOT2_SPEC).map(Self::from_fields)
    }

    /// TLV の [`KekSlotEntry`] へ変換する。
    ///
    /// # Errors
    ///
    /// スロットエントリ長制限を超過する場合は [`VaultError::Parse`] を返す。
    pub fn to_slot_entry(&self) -> Result<KekSlotEntry, VaultError> {
        self.as_fields().to_slot_entry(&SLOT2_SPEC)
    }
}

/// Slot 0 用の Argon2id パラメータがアルゴリズム, 出力長, 安全上限の要件を満たすかを検証する。
///
/// # Errors
///
/// 要件を満たさない場合は [`CryptoError::InvalidParameter`] または [`CryptoError::InvalidKeySize`] を返す。
pub fn validate_slot0_argon2_params(params: &Argon2Params) -> Result<(), CryptoError> {
    if params.output_len() != DEK_LEN {
        return Err(CryptoError::InvalidKeySize);
    }
    if params.algorithm() != argon2::Algorithm::Argon2id
        || params.version() != argon2::Version::V0x13
    {
        return Err(CryptoError::InvalidParameter);
    }
    if params.m_cost() > MAX_SLOT0_M_COST
        || params.t_cost() > MAX_SLOT0_T_COST
        || params.p_cost() > MAX_SLOT0_P_COST
    {
        return Err(CryptoError::InvalidParameter);
    }
    params.validate()
}

/// 固定長プレフィックス長と可変長 `vault_aad` の合計長を検証して返す。
#[inline]
// 32-bit環境ではMAX_AAD_LENがusize::MAXとなり比較が恒偽になるが、環境非依存の単一コードパス維持のため許可する。
#[allow(clippy::absurd_extreme_comparisons)]
fn checked_aad_len(fixed_len: usize, vault_aad: &[u8]) -> Result<usize, CryptoError> {
    let total_len = fixed_len
        .checked_add(vault_aad.len())
        .ok_or(CryptoError::InvalidSliceLength)?;
    if total_len > MAX_AAD_LEN {
        return Err(CryptoError::InvalidSliceLength);
    }
    Ok(total_len)
}

/// Slot 0 (Argon2id) のスタック AAD バッファ容量 (64バイト)。
///
/// 固定ヘッダー長 ([`SLOT0_AAD_FIXED_LEN`] = 48B) と通常の Vault ヘッダー AAD
/// ([`VAULT_HEADER_LEN`] = 14B) の合計 62 バイトをスタック上で完全収容する。
const SLOT0_AAD_STACK_CAP: usize = 64;

/// Slot 1 / Slot 2 (HKDF-SHA256) のスタック AAD バッファ容量 (68バイト)。
///
/// 固定ヘッダー長 ([`HKDF_SLOT_AAD_FIXED_LEN`] = 52B) と通常の Vault ヘッダー AAD
/// ([`VAULT_HEADER_LEN`] = 14B) の合計 66 バイトをスタック上で完全収容する。
const HKDF_SLOT_AAD_STACK_CAP: usize = 68;

const _: () = assert!(SLOT0_AAD_STACK_CAP >= SLOT0_AAD_FIXED_LEN + VAULT_HEADER_LEN);
const _: () = assert!(HKDF_SLOT_AAD_STACK_CAP >= HKDF_SLOT_AAD_FIXED_LEN + VAULT_HEADER_LEN);

/// Slot 0 の AAD バッファ型。
type Slot0AadBuffer = AadBuffer<SLOT0_AAD_STACK_CAP>;

/// Slot 1 / Slot 2 の AAD バッファ型。
type HkdfSlotAadBuffer = AadBuffer<HKDF_SLOT_AAD_STACK_CAP>;

/// AEAD 関連データ (AAD) 構築用のゼロアロケーション指向バッファ。
///
/// 通常時はスタック上の固定長配列バッファを使用し、指定された `total_len` が
/// `STACK_CAP` を超過する場合のみヒープ ([`alloc::vec::Vec`]) にフォールバックする。
#[derive(Debug, Clone, PartialEq, Eq)]
enum AadBuffer<const STACK_CAP: usize> {
    Stack { buf: [u8; STACK_CAP], len: usize },
    Heap(alloc::vec::Vec<u8>),
}

impl<const STACK_CAP: usize> AadBuffer<STACK_CAP> {
    #[inline]
    fn new(total_len: usize) -> Self {
        if total_len <= STACK_CAP {
            Self::Stack {
                buf: [0u8; STACK_CAP],
                len: 0,
            }
        } else {
            Self::Heap(alloc::vec::Vec::with_capacity(total_len))
        }
    }

    #[inline]
    fn push(&mut self, byte: u8) {
        match self {
            Self::Stack { buf, len } => {
                buf[*len] = byte;
                *len += 1;
            }
            Self::Heap(vec) => vec.push(byte),
        }
    }

    #[inline]
    fn extend_from_slice(&mut self, data: &[u8]) {
        match self {
            Self::Stack { buf, len } => {
                let end = *len + data.len();
                buf[*len..end].copy_from_slice(data);
                *len = end;
            }
            Self::Heap(vec) => vec.extend_from_slice(data),
        }
    }

    #[inline]
    #[must_use]
    fn as_slice(&self) -> &[u8] {
        match self {
            Self::Stack { buf, len } => &buf[..*len],
            Self::Heap(vec) => vec.as_slice(),
        }
    }

    #[cfg(test)]
    #[inline]
    #[must_use]
    pub(crate) const fn is_stack(&self) -> bool {
        match self {
            Self::Stack { .. } => true,
            Self::Heap(_) => false,
        }
    }
}

impl<const STACK_CAP: usize> Default for AadBuffer<STACK_CAP> {
    #[inline]
    fn default() -> Self {
        Self::new(0)
    }
}

impl<const STACK_CAP: usize> core::ops::Deref for AadBuffer<STACK_CAP> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

/// Slot 0 の暗号化および復号に用いる AEAD 関連データ (AAD) を構築する。
///
/// ドメイン分離プレフィックス, スロット識別子, KDF 種別, Argon2id パラメータ,
/// ソルト, 呼び出し元が指定した `vault_aad` (通常は [`VaultHeader::associated_data`]) を結合し、
/// パラメータのダウングレード攻撃やヘッダーとスロットの間のすり替えを検知する。
/// 通常時はスタックバッファ ([`Slot0AadBuffer`]) 内でゼロアロケーションにて構築される。
fn build_slot0_aad(
    params: &Argon2Params,
    salt: &[u8; SLOT0_SALT_LEN],
    vault_aad: &[u8],
) -> Result<Slot0AadBuffer, CryptoError> {
    let total_len = checked_aad_len(SLOT0_AAD_FIXED_LEN, vault_aad)?;

    let mut aad = Slot0AadBuffer::new(total_len);
    aad.extend_from_slice(SLOT0_AAD_PREFIX);
    aad.push(SLOT_ID_ARGON2ID);
    aad.push(KDF_KIND_ARGON2ID);
    aad.extend_from_slice(&params.m_cost().to_be_bytes());
    aad.extend_from_slice(&params.t_cost().to_be_bytes());
    aad.extend_from_slice(&params.p_cost().to_be_bytes());
    aad.extend_from_slice(salt);
    aad.extend_from_slice(vault_aad);
    Ok(aad)
}

/// Slot 0 (Argon2id マスターパスワード) により KEK を導出し、256-bit DEK を暗号化ラップする。
///
/// `vault_aad` には通常 [`VaultHeader::associated_data`] を渡し、
/// Vault ヘッダーとの暗号学的バインディングを確立する。
///
/// # Errors
///
/// - Argon2id パラメータが不正な場合は [`VaultError::Crypto`] ([`CryptoError::InvalidParameter`]) などを返す。
/// - `vault_aad` 長が許容上限を超過する場合は [`VaultError::Crypto`] ([`CryptoError::InvalidSliceLength`]) を返す。
/// - 鍵導出または AEAD 暗号化に失敗した場合は [`VaultError::Crypto`] を返す。
pub fn wrap_dek_slot0(
    dek: &SecretBytes<DEK_LEN>,
    password: &[u8],
    salt: &[u8; SLOT0_SALT_LEN],
    nonce: &[u8; SLOT0_NONCE_LEN],
    params: &Argon2Params,
    vault_aad: &[u8],
) -> Result<KekSlotEntry, VaultError> {
    wrap_dek_slot0_with_secret(dek, password, salt, nonce, params, &[], vault_aad)
}

/// 導出済み KEK を用いて 256-bit DEK を XChaCha20-Poly1305 で暗号化ラップする共通コア。
///
/// KEK は [`VaultCipher::from_consumed_secret`] により直ちにゼロ消去され、
/// 作業バッファも正常終了時とエラー終了時を問わず確実に [`volatile_zeroize`] で消去する。
fn wrap_dek_with_kek(
    dek: &SecretBytes<DEK_LEN>,
    kek: &mut SecretBytes<DEK_LEN>,
    nonce: &[u8; XCHACHA20_POLY1305_NONCE_LEN],
    aad: &[u8],
) -> Result<([u8; DEK_LEN], [u8; TAG_LEN]), VaultError> {
    let cipher = VaultCipher::from_consumed_secret(SLOT_CIPHER_SUITE, kek);

    let mut work_buf = SecretBytes::new(*dek.as_bytes());
    let encrypt_res = cipher.encrypt_in_place_detached(nonce, aad, work_buf.as_mut_slice());
    let auth_tag = match encrypt_res {
        Ok(tag) => tag,
        Err(err) => {
            volatile_zeroize(work_buf.as_mut_slice());
            return Err(VaultError::Crypto(err));
        }
    };

    let ciphertext = *work_buf.as_bytes();
    volatile_zeroize(work_buf.as_mut_slice());
    Ok((ciphertext, auth_tag))
}

/// 導出済み KEK を用いて暗号化済み DEK を XChaCha20-Poly1305 で認証復号する共通コア。
///
/// KEK は [`VaultCipher::from_consumed_secret`] により直ちにゼロ消去され、
/// 失敗時の DEK 作業バッファも直ちに [`volatile_zeroize`] で消去する。
fn unwrap_dek_with_kek(
    kek: &mut SecretBytes<DEK_LEN>,
    nonce: &[u8; XCHACHA20_POLY1305_NONCE_LEN],
    aad: &[u8],
    ciphertext: &[u8; DEK_LEN],
    auth_tag: &[u8; TAG_LEN],
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    let cipher = VaultCipher::from_consumed_secret(SLOT_CIPHER_SUITE, kek);

    let mut dek = SecretBytes::new(*ciphertext);
    if let Err(err) = cipher.decrypt_in_place_detached_tag(nonce, aad, dek.as_mut_slice(), auth_tag)
    {
        volatile_zeroize(dek.as_mut_slice());
        return Err(VaultError::Crypto(err));
    }

    Ok(dek)
}

/// ペッパー (`secret`) を併用し、Slot 0 により KEK を導出して 256-bit DEK を暗号化ラップする。
///
/// 処理中に生成される KEK および作業バッファは, [`SecretBytes`] と [`volatile_zeroize`] により、
/// 正常終了時とエラー終了時を問わず確実にゼロ消去される。
///
/// # Errors
///
/// - パラメータ検証, AAD 構築, 鍵導出, AEAD 暗号化のいずれかに失敗した場合は対応する [`VaultError`] を返す。
pub fn wrap_dek_slot0_with_secret(
    dek: &SecretBytes<DEK_LEN>,
    password: &[u8],
    salt: &[u8; SLOT0_SALT_LEN],
    nonce: &[u8; SLOT0_NONCE_LEN],
    params: &Argon2Params,
    secret: &[u8],
    vault_aad: &[u8],
) -> Result<KekSlotEntry, VaultError> {
    validate_slot0_argon2_params(params)?;
    let aad = build_slot0_aad(params, salt, vault_aad)?;

    let mut kek = params.derive_key_32_with_secret(password, salt, secret)?;
    let (ciphertext, auth_tag) = wrap_dek_with_kek(dek, &mut kek, nonce, &aad)?;

    let payload = Argon2idSlotPayload {
        params: *params,
        salt: *salt,
        nonce: *nonce,
        ciphertext,
        auth_tag,
    };

    payload.to_slot_entry()
}

/// [`VaultHeader`] を関連データとしてバインドし、Slot 0 により 256-bit DEK を暗号化ラップする。
///
/// # Errors
///
/// ラップ処理に失敗した場合は対応する [`VaultError`] を返す。
#[inline]
pub fn wrap_dek_slot0_for_header(
    dek: &SecretBytes<DEK_LEN>,
    password: &[u8],
    salt: &[u8; SLOT0_SALT_LEN],
    nonce: &[u8; SLOT0_NONCE_LEN],
    params: &Argon2Params,
    header: &VaultHeader,
) -> Result<KekSlotEntry, VaultError> {
    wrap_dek_slot0(
        dek,
        password,
        salt,
        nonce,
        params,
        &header.associated_data(),
    )
}

/// Slot 0 の暗号化エントリから Argon2id により KEK を再導出し、256-bit DEK を復号する。
///
/// 復号に失敗した場合、中間 KEK および DEK 作業バッファは即座にゼロ消去される。
///
/// # Errors
///
/// - スロット形式または Argon2id パラメータが不正な場合は [`VaultError::Parse`] または [`VaultError::Crypto`] を返す。
/// - パスワード不一致, AAD 不一致, データ改ざんにより認証タグ照合に失敗した場合は、
///   [`VaultError::Crypto`] ([`CryptoError::AeadDecryptionFailed`]) を返す。
pub fn unwrap_dek_slot0(
    entry: &KekSlotEntry,
    password: &[u8],
    vault_aad: &[u8],
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    unwrap_dek_slot0_with_secret(entry, password, &[], vault_aad)
}

/// ペッパー (`secret`) を併用し、Slot 0 の暗号化エントリから 256-bit DEK を復号する。
///
/// # Errors
///
/// スロット検証, AAD 構築, 鍵導出, AEAD 認証復号のいずれかに失敗した場合は対応する [`VaultError`] を返す。
pub fn unwrap_dek_slot0_with_secret(
    entry: &KekSlotEntry,
    password: &[u8],
    secret: &[u8],
    vault_aad: &[u8],
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    let payload = Argon2idSlotPayload::from_slot_entry(entry)?;
    let aad = build_slot0_aad(&payload.params, &payload.salt, vault_aad)?;

    let mut kek = payload
        .params
        .derive_key_32_with_secret(password, &payload.salt, secret)?;
    unwrap_dek_with_kek(
        &mut kek,
        &payload.nonce,
        &aad,
        &payload.ciphertext,
        &payload.auth_tag,
    )
}

/// [`VaultHeader`] を関連データとしてバインドし、Slot 0 の暗号化エントリから 256-bit DEK を復号する。
///
/// # Errors
///
/// 復号処理に失敗した場合は対応する [`VaultError`] を返す。
#[inline]
pub fn unwrap_dek_slot0_for_header(
    entry: &KekSlotEntry,
    password: &[u8],
    header: &VaultHeader,
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    unwrap_dek_slot0(entry, password, &header.associated_data())
}

/// スロットエントリのフォーマットおよびパラメータが、Slot 0 (Argon2id) として有効かを判定する。
#[must_use]
pub fn is_valid_slot0_entry(entry: &KekSlotEntry) -> bool {
    Argon2idSlotPayload::from_slot_entry(entry).is_ok()
}

/// Slot 1 および Slot 2 に共通する HKDF スロット用 AEAD 関連データ (AAD) を構築する。
/// 通常時はスタックバッファ ([`HkdfSlotAadBuffer`]) 内でゼロアロケーションにて構築される。
fn build_hkdf_slot_aad(
    spec: &HkdfSlotSpec,
    salt: &[u8; SLOT1_SALT_LEN],
    vault_aad: &[u8],
) -> Result<HkdfSlotAadBuffer, CryptoError> {
    let total_len = checked_aad_len(HKDF_SLOT_AAD_FIXED_LEN, vault_aad)?;

    let mut aad = HkdfSlotAadBuffer::new(total_len);
    aad.extend_from_slice(spec.aad_prefix);
    aad.push(spec.slot_id);
    aad.push(spec.kdf_kind);
    aad.extend_from_slice(salt);
    aad.extend_from_slice(vault_aad);
    Ok(aad)
}

/// Slot 1 および Slot 2 に共通する HKDF-SHA256 鍵導出および DEK ラップ処理を実行する。
fn wrap_dek_hkdf_slot(
    spec: &HkdfSlotSpec,
    dek: &SecretBytes<DEK_LEN>,
    ikm: &[u8],
    salt: &[u8; SLOT1_SALT_LEN],
    nonce: &[u8; SLOT1_NONCE_LEN],
    vault_aad: &[u8],
) -> Result<KekSlotEntry, VaultError> {
    if ikm.len() < spec.min_secret_len {
        return Err(VaultError::Crypto(CryptoError::InvalidKeySize));
    }

    let aad = build_hkdf_slot_aad(spec, salt, vault_aad)?;
    let mut kek = hkdf_sha256_derive_32(salt, ikm, spec.hkdf_info)?;
    let (ciphertext, auth_tag) = wrap_dek_with_kek(dek, &mut kek, nonce, &aad)?;

    let fields = HkdfSlotFields {
        salt: *salt,
        nonce: *nonce,
        ciphertext,
        auth_tag,
    };
    fields.to_slot_entry(spec)
}

/// Slot 1 および Slot 2 に共通する HKDF-SHA256 鍵再導出および DEK 認証復号処理を実行する。
fn unwrap_dek_hkdf_slot(
    spec: &HkdfSlotSpec,
    entry: &KekSlotEntry,
    ikm: &[u8],
    vault_aad: &[u8],
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    let fields = HkdfSlotFields::from_slot_entry(entry, spec)?;
    if ikm.len() < spec.min_secret_len {
        return Err(VaultError::Crypto(CryptoError::InvalidKeySize));
    }

    let aad = build_hkdf_slot_aad(spec, &fields.salt, vault_aad)?;
    let mut kek = hkdf_sha256_derive_32(&fields.salt, ikm, spec.hkdf_info)?;
    unwrap_dek_with_kek(
        &mut kek,
        &fields.nonce,
        &aad,
        &fields.ciphertext,
        &fields.auth_tag,
    )
}

/// Slot 1 (WebAuthn PRF / HKDF-SHA256) により KEK を導出し、256-bit DEK を暗号化ラップする。
///
/// `prf_secret` には WebAuthn PRF 拡張から取得した 32バイト以上の高エントロピー出力を指定する。
/// `vault_aad` には通常 [`VaultHeader::associated_data`] を渡し、Vault ヘッダーと暗号学的に結合する。
///
/// # Errors
///
/// - `prf_secret` が [`SLOT1_MIN_PRF_LEN`] (32バイト) 未満の場合は [`VaultError::Crypto`] ([`CryptoError::InvalidKeySize`]) を返す。
/// - `vault_aad` 長が許容上限を超過する場合は [`VaultError::Crypto`] ([`CryptoError::InvalidSliceLength`]) を返す。
/// - 鍵導出または AEAD 暗号化に失敗した場合は [`VaultError::Crypto`] を返す。
pub fn wrap_dek_slot1(
    dek: &SecretBytes<DEK_LEN>,
    prf_secret: &[u8],
    salt: &[u8; SLOT1_SALT_LEN],
    nonce: &[u8; SLOT1_NONCE_LEN],
    vault_aad: &[u8],
) -> Result<KekSlotEntry, VaultError> {
    wrap_dek_hkdf_slot(&SLOT1_SPEC, dek, prf_secret, salt, nonce, vault_aad)
}

/// [`VaultHeader`] を関連データとしてバインドし、Slot 1 により 256-bit DEK を暗号化ラップする。
///
/// # Errors
///
/// ラップ処理に失敗した場合は対応する [`VaultError`] を返す。
#[inline]
pub fn wrap_dek_slot1_for_header(
    dek: &SecretBytes<DEK_LEN>,
    prf_secret: &[u8],
    salt: &[u8; SLOT1_SALT_LEN],
    nonce: &[u8; SLOT1_NONCE_LEN],
    header: &VaultHeader,
) -> Result<KekSlotEntry, VaultError> {
    wrap_dek_slot1(dek, prf_secret, salt, nonce, &header.associated_data())
}

/// Slot 1 の暗号化エントリから HKDF-SHA256 により KEK を再導出し、256-bit DEK を復号する。
///
/// # Errors
///
/// - スロット形式または長さが不正な場合は [`VaultError::Parse`] を返す。
/// - `prf_secret` が [`SLOT1_MIN_PRF_LEN`] 未満の場合は [`VaultError::Crypto`] ([`CryptoError::InvalidKeySize`]) を返す。
/// - PRF シークレット不一致, AAD 不一致, 改ざんによるタグ照合失敗時は、
///   [`VaultError::Crypto`] ([`CryptoError::AeadDecryptionFailed`]) を返す。
pub fn unwrap_dek_slot1(
    entry: &KekSlotEntry,
    prf_secret: &[u8],
    vault_aad: &[u8],
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    unwrap_dek_hkdf_slot(&SLOT1_SPEC, entry, prf_secret, vault_aad)
}

/// [`VaultHeader`] を関連データとしてバインドし、Slot 1 の暗号化エントリから 256-bit DEK を復号する。
///
/// # Errors
///
/// 復号処理に失敗した場合は対応する [`VaultError`] を返す。
#[inline]
pub fn unwrap_dek_slot1_for_header(
    entry: &KekSlotEntry,
    prf_secret: &[u8],
    header: &VaultHeader,
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    unwrap_dek_slot1(entry, prf_secret, &header.associated_data())
}

/// スロットエントリのフォーマットが Slot 1 (WebAuthn PRF / HKDF-SHA256) として有効かを判定する。
#[must_use]
pub fn is_valid_slot1_entry(entry: &KekSlotEntry) -> bool {
    PrfSlotPayload::from_slot_entry(entry).is_ok()
}

/// 整形済み英数字リカバリーコード (ハイフン・空白区切り・大小混在可) を正準化する。
///
/// ASCII の `'-'` および `' '` を区切り文字として除去し、ASCII 英小文字 (`a..=z`) を大文字へ統一する。
/// 制御文字や非英数字記号が含まれる場合や、正準化後の長さが [`SLOT2_MIN_CODE_LEN`] 未満の場合は、
/// 作業バッファを直ちにゼロ消去した上でエラーを返す。
///
/// # Errors
///
/// - 入力長が許容上限 (512バイト) を超える場合は [`VaultError::Crypto`] ([`CryptoError::InvalidSliceLength`]) を返す。
/// - 英数字および `'-'` / `' '` 以外の不正文字が含まれる場合は [`VaultError::Crypto`] ([`CryptoError::InvalidParameter`]) を返す。
/// - 正準化後の文字数が [`SLOT2_MIN_CODE_LEN`] (24文字) 未満の場合は [`VaultError::Crypto`] ([`CryptoError::InvalidKeySize`]) を返す。
pub fn normalize_recovery_code(code: &[u8]) -> Result<SecretVec, VaultError> {
    if code.len() > MAX_RECOVERY_CODE_INPUT_LEN {
        return Err(VaultError::Crypto(CryptoError::InvalidSliceLength));
    }

    let mut normalized = SecretVec::with_capacity(code.len());
    for &byte in code {
        if byte == b'-' || byte == b' ' {
            continue;
        }
        if byte.is_ascii_alphanumeric() {
            normalized.push(byte.to_ascii_uppercase());
        } else {
            volatile_zeroize(normalized.as_mut_slice());
            return Err(VaultError::Crypto(CryptoError::InvalidParameter));
        }
    }

    if normalized.len() < SLOT2_MIN_CODE_LEN {
        volatile_zeroize(normalized.as_mut_slice());
        return Err(VaultError::Crypto(CryptoError::InvalidKeySize));
    }

    Ok(normalized)
}

/// Slot 2 (高エントロピーリカバリーシークレット) により KEK を導出し、256-bit DEK を暗号化ラップする。
///
/// `recovery_secret` には [`SLOT2_MIN_SECRET_LEN`] (16バイト = 128ビット) 以上の高エントロピー鍵素材を指定する。
/// 整形済み英数字コードを用いる場合は [`wrap_dek_slot2_code`] を使用する。
///
/// # Errors
///
/// - `recovery_secret` が [`SLOT2_MIN_SECRET_LEN`] 未満の場合は [`VaultError::Crypto`] ([`CryptoError::InvalidKeySize`]) を返す。
/// - `vault_aad` 長が許容上限を超過する場合は [`VaultError::Crypto`] ([`CryptoError::InvalidSliceLength`]) を返す。
/// - 鍵導出または AEAD 暗号化に失敗した場合は [`VaultError::Crypto`] を返す。
pub fn wrap_dek_slot2(
    dek: &SecretBytes<DEK_LEN>,
    recovery_secret: &[u8],
    salt: &[u8; SLOT2_SALT_LEN],
    nonce: &[u8; SLOT2_NONCE_LEN],
    vault_aad: &[u8],
) -> Result<KekSlotEntry, VaultError> {
    wrap_dek_hkdf_slot(&SLOT2_SPEC, dek, recovery_secret, salt, nonce, vault_aad)
}

/// [`VaultHeader`] を関連データとしてバインドし、Slot 2 により 256-bit DEK を暗号化ラップする。
///
/// # Errors
///
/// ラップ処理に失敗した場合は対応する [`VaultError`] を返す。
#[inline]
pub fn wrap_dek_slot2_for_header(
    dek: &SecretBytes<DEK_LEN>,
    recovery_secret: &[u8],
    salt: &[u8; SLOT2_SALT_LEN],
    nonce: &[u8; SLOT2_NONCE_LEN],
    header: &VaultHeader,
) -> Result<KekSlotEntry, VaultError> {
    wrap_dek_slot2(dek, recovery_secret, salt, nonce, &header.associated_data())
}

/// 整形済み英数字リカバリーコードを正準化した上で、Slot 2 により 256-bit DEK を暗号化ラップする。
///
/// 正準化で生成された中間バッファは、RAII および明示的 [`volatile_zeroize`] により即座にゼロ消去する。
///
/// # Errors
///
/// [`normalize_recovery_code`] または [`wrap_dek_slot2`] が失敗した場合は対応する [`VaultError`] を返す。
pub fn wrap_dek_slot2_code(
    dek: &SecretBytes<DEK_LEN>,
    recovery_code: &[u8],
    salt: &[u8; SLOT2_SALT_LEN],
    nonce: &[u8; SLOT2_NONCE_LEN],
    vault_aad: &[u8],
) -> Result<KekSlotEntry, VaultError> {
    let mut normalized = normalize_recovery_code(recovery_code)?;
    let res = wrap_dek_slot2(dek, normalized.as_slice(), salt, nonce, vault_aad);
    volatile_zeroize(normalized.as_mut_slice());
    res
}

/// [`VaultHeader`] を関連データとしてバインドし、整形済みリカバリーコードで Slot 2 を暗号化ラップする。
///
/// # Errors
///
/// ラップ処理に失敗した場合は対応する [`VaultError`] を返す。
#[inline]
pub fn wrap_dek_slot2_code_for_header(
    dek: &SecretBytes<DEK_LEN>,
    recovery_code: &[u8],
    salt: &[u8; SLOT2_SALT_LEN],
    nonce: &[u8; SLOT2_NONCE_LEN],
    header: &VaultHeader,
) -> Result<KekSlotEntry, VaultError> {
    wrap_dek_slot2_code(dek, recovery_code, salt, nonce, &header.associated_data())
}

/// Slot 2 の暗号化エントリから生リカバリーシークレットを用いて 256-bit DEK を復号する。
///
/// # Errors
///
/// - スロット形式または長さが不正な場合は [`VaultError::Parse`] を返す。
/// - `recovery_secret` が [`SLOT2_MIN_SECRET_LEN`] 未満の場合は [`VaultError::Crypto`] ([`CryptoError::InvalidKeySize`]) を返す。
/// - リカバリーシークレット不一致, AAD 不一致, 改ざんによるタグ照合失敗時は、
///   [`VaultError::Crypto`] ([`CryptoError::AeadDecryptionFailed`]) を返す。
pub fn unwrap_dek_slot2(
    entry: &KekSlotEntry,
    recovery_secret: &[u8],
    vault_aad: &[u8],
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    unwrap_dek_hkdf_slot(&SLOT2_SPEC, entry, recovery_secret, vault_aad)
}

/// [`VaultHeader`] を関連データとしてバインドし、Slot 2 の暗号化エントリから 256-bit DEK を復号する。
///
/// # Errors
///
/// 復号処理に失敗した場合は対応する [`VaultError`] を返す。
#[inline]
pub fn unwrap_dek_slot2_for_header(
    entry: &KekSlotEntry,
    recovery_secret: &[u8],
    header: &VaultHeader,
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    unwrap_dek_slot2(entry, recovery_secret, &header.associated_data())
}

/// 整形済み英数字リカバリーコードを正準化した上で、Slot 2 の暗号化エントリから 256-bit DEK を復号する。
///
/// # Errors
///
/// [`normalize_recovery_code`] または [`unwrap_dek_slot2`] が失敗した場合は対応する [`VaultError`] を返す。
pub fn unwrap_dek_slot2_code(
    entry: &KekSlotEntry,
    recovery_code: &[u8],
    vault_aad: &[u8],
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    let mut normalized = normalize_recovery_code(recovery_code)?;
    let res = unwrap_dek_slot2(entry, normalized.as_slice(), vault_aad);
    volatile_zeroize(normalized.as_mut_slice());
    res
}

/// [`VaultHeader`] を関連データとしてバインドし、整形済みリカバリーコードで Slot 2 を復号する。
///
/// # Errors
///
/// 復号処理に失敗した場合は対応する [`VaultError`] を返す。
#[inline]
pub fn unwrap_dek_slot2_code_for_header(
    entry: &KekSlotEntry,
    recovery_code: &[u8],
    header: &VaultHeader,
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    unwrap_dek_slot2_code(entry, recovery_code, &header.associated_data())
}

/// スロットエントリのフォーマットが Slot 2 (リカバリーコード) として有効かを判定する。
#[must_use]
pub fn is_valid_slot2_entry(entry: &KekSlotEntry) -> bool {
    RecoverySlotPayload::from_slot_entry(entry).is_ok()
}

/// TLV スロットエントリ一覧から指定された `slot_id` に一致する単一エントリを検索する。
///
/// 同一 `slot_id` の重複エントリが存在する場合はフォーマット不正として拒絶する。
///
/// # Errors
///
/// - 該当スロットが見つからない場合は [`VaultError::SlotNotFound`] を返す。
/// - 同一 `slot_id` のエントリが重複している場合は [`VaultError::Parse`] ([`TlvParseError::InvalidFormat`]) を返す。
pub fn find_slot_entry(entries: &[KekSlotEntry], slot_id: u8) -> Result<&KekSlotEntry, VaultError> {
    let mut found: Option<&KekSlotEntry> = None;
    for entry in entries {
        if entry.slot_id() == slot_id {
            if found.is_some() {
                return Err(VaultError::Parse(TlvParseError::InvalidFormat));
            }
            found = Some(entry);
        }
    }
    found.ok_or(VaultError::SlotNotFound)
}

/// TLV の [`KekSlotEntry`] スライスを検査し、[`KekSlots`] の健全性モデルを構築する。
///
/// 各スロット ID (`0`, `1`, `2`) について、未設定, 有効, 無効 (または重複) を判定する。
/// Slot 0 についてはフォーマット長, KDF 種別, Argon2id パラメータの境界まで検証する。
#[must_use]
pub fn inspect_kek_slots(entries: &[KekSlotEntry]) -> KekSlots {
    let mut slots = KekSlots::unset_all();
    let mut seen = [false; SlotKind::COUNT];

    for entry in entries {
        let Ok(kind) = SlotKind::from_slot_id(entry.slot_id()) else {
            continue;
        };
        let idx = kind.as_slot_id() as usize;
        if seen[idx] {
            // 同一スロットIDの重複は不正な構成として Invalid に設定する。
            slots.set_status(kind, SlotStatus::Invalid);
            continue;
        }
        seen[idx] = true;

        let status = match kind {
            SlotKind::Argon2id => {
                if is_valid_slot0_entry(entry) {
                    SlotStatus::Valid
                } else {
                    SlotStatus::Invalid
                }
            }
            SlotKind::Prf => {
                if is_valid_slot1_entry(entry) {
                    SlotStatus::Valid
                } else {
                    SlotStatus::Invalid
                }
            }
            SlotKind::Recovery => {
                if is_valid_slot2_entry(entry) {
                    SlotStatus::Valid
                } else {
                    SlotStatus::Invalid
                }
            }
        };
        slots.set_status(kind, status);
    }

    slots
}

/// Vault 解錠試行時に呼び出し元が提示する各 KEK スロット向けの認証資格情報。
#[derive(Clone, Copy)]
pub enum SlotCredential<'a> {
    /// Slot 0: Argon2id マスターパスワードおよび任意ペッパー。
    Password {
        /// マスターパスワードバイト列。
        password: &'a [u8],
        /// 任意ペッパーシークレット。
        secret: &'a [u8],
    },
    /// Slot 1: WebAuthn PRF 出力シークレット。
    Prf(&'a [u8]),
    /// Slot 2: 生の高エントロピーリカバリーシークレット。
    Recovery(&'a [u8]),
    /// Slot 2: 整形済み英数字リカバリーコード (正準化対象)。
    RecoveryCode(&'a [u8]),
}

impl<'a> SlotCredential<'a> {
    /// ペッパーなしの Slot 0 パスワード資格情報を生成する。
    #[inline]
    #[must_use]
    pub const fn password(password: &'a [u8]) -> Self {
        Self::Password {
            password,
            secret: &[],
        }
    }

    /// ペッパー併用の Slot 0 パスワード資格情報を生成する。
    #[inline]
    #[must_use]
    pub const fn password_with_secret(password: &'a [u8], secret: &'a [u8]) -> Self {
        Self::Password { password, secret }
    }

    /// Slot 1 (WebAuthn PRF) 資格情報を生成する。
    #[inline]
    #[must_use]
    pub const fn prf(prf_secret: &'a [u8]) -> Self {
        Self::Prf(prf_secret)
    }

    /// Slot 2 (生リカバリーシークレット) 資格情報を生成する。
    #[inline]
    #[must_use]
    pub const fn recovery(recovery_secret: &'a [u8]) -> Self {
        Self::Recovery(recovery_secret)
    }

    /// Slot 2 (整形済みリカバリーコード) 資格情報を生成する。
    #[inline]
    #[must_use]
    pub const fn recovery_code(recovery_code: &'a [u8]) -> Self {
        Self::RecoveryCode(recovery_code)
    }

    /// 資格情報に対応する [`SlotKind`] を返す。
    #[inline]
    #[must_use]
    pub const fn slot_kind(self) -> SlotKind {
        match self {
            Self::Password { .. } => SlotKind::Argon2id,
            Self::Prf(_) => SlotKind::Prf,
            Self::Recovery(_) | Self::RecoveryCode(_) => SlotKind::Recovery,
        }
    }
}

impl core::fmt::Debug for SlotCredential<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Password { .. } => f.write_str("SlotCredential::Password([REDACTED])"),
            Self::Prf(_) => f.write_str("SlotCredential::Prf([REDACTED])"),
            Self::Recovery(_) => f.write_str("SlotCredential::Recovery([REDACTED])"),
            Self::RecoveryCode(_) => f.write_str("SlotCredential::RecoveryCode([REDACTED])"),
        }
    }
}

/// 解錠パイプライン内で実行された実暗号演算およびダミー暗号演算の実行回数記録。
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct SlotEvalTrace {
    real_argon2id_ops: usize,
    dummy_argon2id_ops: usize,
    real_hkdf_ops: usize,
    dummy_hkdf_ops: usize,
    real_aead_ops: usize,
    dummy_aead_ops: usize,
}

#[cfg(test)]
impl SlotEvalTrace {
    const fn argon2id_ops(self) -> usize {
        self.real_argon2id_ops + self.dummy_argon2id_ops
    }

    const fn hkdf_ops(self) -> usize {
        self.real_hkdf_ops + self.dummy_hkdf_ops
    }

    const fn total_kdf_ops(self) -> usize {
        self.argon2id_ops() + self.hkdf_ops()
    }

    const fn total_aead_ops(self) -> usize {
        self.real_aead_ops + self.dummy_aead_ops
    }
}

/// コンパイラ最適化によるダミー暗号演算の除去 (DCE) を防ぎつつ、
/// KEK とダミー復号結果のメモリを即座に揮発性ゼロ消去する。
fn consume_dummy_aead_unwrap(
    kek: &mut SecretBytes<DEK_LEN>,
    aad: &[u8],
    trace: &mut SlotEvalTrace,
) {
    trace.dummy_aead_ops += 1;
    let res = unwrap_dek_with_kek(kek, &DUMMY_NONCE, aad, &DUMMY_CIPHERTEXT, &DUMMY_TAG);
    match res {
        Ok(mut unexpected_dek) => {
            // 万一タグ照合が偶然通過した場合も結果を観測不能化し即座に破棄する。
            let _ = core::hint::black_box(unexpected_dek.as_bytes()[0]);
            volatile_zeroize(unexpected_dek.as_mut_slice());
        }
        Err(err) => {
            let _ = core::hint::black_box(err);
        }
    }
}

/// ダミー KEK シードを用いて XChaCha20-Poly1305 AEAD 復号のみを実行するフォールバック。
fn dummy_aead_unwrap_traced(aad: &[u8], trace: &mut SlotEvalTrace) {
    let mut dummy_kek = SecretBytes::new(DUMMY_KEK_SEED);
    consume_dummy_aead_unwrap(&mut dummy_kek, aad, trace);
}

/// ダミー Slot 0 演算に使用可能な妥当な [`Argon2Params`] を解決する。
fn resolve_valid_argon2_params(params: &Argon2Params) -> Argon2Params {
    if validate_slot0_argon2_params(params).is_ok() && params.output_len() == DEK_LEN {
        *params
    } else {
        Argon2Params::default_for_target()
    }
}

/// AAD 長上限超過時にも確実に AAD バイト列を構築する Slot 0 ダミー用ヘルパー。
fn resolve_safe_slot0_aad(
    params: &Argon2Params,
    salt: &[u8; SLOT0_SALT_LEN],
    vault_aad: &[u8],
) -> Slot0AadBuffer {
    match build_slot0_aad(params, salt, vault_aad) {
        Ok(aad) => aad,
        Err(_) => build_slot0_aad(params, salt, &[]).unwrap_or_default(),
    }
}

/// AAD 長上限超過時にも確実に AAD バイト列を構築する HKDF スロットダミー用ヘルパー。
fn resolve_safe_hkdf_aad(
    spec: &HkdfSlotSpec,
    salt: &[u8; SLOT1_SALT_LEN],
    vault_aad: &[u8],
) -> HkdfSlotAadBuffer {
    match build_hkdf_slot_aad(spec, salt, vault_aad) {
        Ok(aad) => aad,
        Err(_) => build_hkdf_slot_aad(spec, salt, &[]).unwrap_or_default(),
    }
}

/// Slot 0 (Argon2id + XChaCha20-Poly1305) と同等コストのダミー暗号演算を 1 回実行する。
fn dummy_unwrap_slot0_traced(params: &Argon2Params, vault_aad: &[u8], trace: &mut SlotEvalTrace) {
    let effective_params = resolve_valid_argon2_params(params);
    let aad = resolve_safe_slot0_aad(&effective_params, &DUMMY_SLOT0_SALT, vault_aad);
    trace.dummy_argon2id_ops += 1;

    match effective_params.derive_key_32_with_secret(DUMMY_SLOT0_PASSWORD, &DUMMY_SLOT0_SALT, &[]) {
        Ok(mut kek) => consume_dummy_aead_unwrap(&mut kek, &aad, trace),
        Err(err) => {
            let _ = core::hint::black_box(err);
            dummy_aead_unwrap_traced(&aad, trace);
        }
    }
}

/// Slot 1 / Slot 2 (HKDF-SHA256 + XChaCha20-Poly1305) と同等コストのダミー暗号演算を 1 回実行する。
fn dummy_unwrap_hkdf_slot_traced(spec: &HkdfSlotSpec, vault_aad: &[u8], trace: &mut SlotEvalTrace) {
    let aad = resolve_safe_hkdf_aad(spec, &DUMMY_HKDF_SALT, vault_aad);
    trace.dummy_hkdf_ops += 1;

    match hkdf_sha256_derive_32(&DUMMY_HKDF_SALT, &DUMMY_HKDF_IKM, spec.hkdf_info) {
        Ok(mut kek) => consume_dummy_aead_unwrap(&mut kek, &aad, trace),
        Err(err) => {
            let _ = core::hint::black_box(err);
            dummy_aead_unwrap_traced(&aad, trace);
        }
    }
}

/// Slot 2 (リカバリーコード正準化 + HKDF-SHA256 + AEAD 復号) のダミー暗号演算を 1 回実行する。
fn dummy_unwrap_slot2_code_traced(vault_aad: &[u8], trace: &mut SlotEvalTrace) {
    if let Ok(mut normalized) = normalize_recovery_code(DUMMY_RECOVERY_CODE) {
        let _ = core::hint::black_box(normalized.len());
        volatile_zeroize(normalized.as_mut_slice());
    }
    dummy_unwrap_hkdf_slot_traced(&SLOT2_SPEC, vault_aad, trace);
}

/// ダミー暗号演算パイプラインの実行回数記録。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DummySlotEvalSummary {
    /// 実行されたダミー Argon2id 演算回数。
    pub dummy_argon2id_ops: usize,
    /// 実行されたダミー HKDF-SHA256 演算回数。
    pub dummy_hkdf_ops: usize,
    /// 実行されたダミー AEAD 復号演算回数。
    pub dummy_aead_ops: usize,
}

/// 静的解析および検査向けに、Slot 0/1/2 のダミー暗号演算パイプラインを実行する。
///
/// コンパイラ最適化によるダミー暗号演算呼び出しの除去 (DCE) を防ぐため、
/// ダミー Argon2id, HKDF-SHA256, AEAD 復号演算を明示的に呼び出し、
/// その実行回数サマリを返す。
#[doc(hidden)]
pub fn run_dummy_slot_eval_for_inspection(vault_aad: &[u8]) -> DummySlotEvalSummary {
    let mut trace = SlotEvalTrace::default();
    dummy_unwrap_slot0_traced(&Argon2Params::default_for_target(), vault_aad, &mut trace);
    dummy_unwrap_hkdf_slot_traced(&SLOT1_SPEC, vault_aad, &mut trace);
    dummy_unwrap_slot2_code_traced(vault_aad, &mut trace);
    let summary = DummySlotEvalSummary {
        dummy_argon2id_ops: trace.dummy_argon2id_ops,
        dummy_hkdf_ops: trace.dummy_hkdf_ops,
        dummy_aead_ops: trace.dummy_aead_ops,
    };
    core::hint::black_box(summary)
}

/// Slot 0 エントリの復号を試行し、不在・無効・フォーマット不正・エラー時はダミー暗号演算で補完する。
fn eval_slot0_or_dummy(
    entry: Option<&KekSlotEntry>,
    is_slot_valid: bool,
    password: &[u8],
    secret: &[u8],
    vault_aad: &[u8],
    fallback_params: &Argon2Params,
    trace: &mut SlotEvalTrace,
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    if !is_slot_valid {
        dummy_unwrap_slot0_traced(fallback_params, vault_aad, trace);
        return Err(VaultError::AuthenticationFailed);
    }

    let Some(slot_entry) = entry else {
        dummy_unwrap_slot0_traced(fallback_params, vault_aad, trace);
        return Err(VaultError::SlotNotFound);
    };

    let payload = match Argon2idSlotPayload::from_slot_entry(slot_entry) {
        Ok(parsed) => parsed,
        Err(parse_err) => {
            dummy_unwrap_slot0_traced(fallback_params, vault_aad, trace);
            return Err(parse_err);
        }
    };

    let aad = match build_slot0_aad(&payload.params, &payload.salt, vault_aad) {
        Ok(aad) => aad,
        Err(err) => {
            dummy_unwrap_slot0_traced(&payload.params, vault_aad, trace);
            return Err(VaultError::Crypto(err));
        }
    };

    let mut kek = match payload
        .params
        .derive_key_32_with_secret(password, &payload.salt, secret)
    {
        Ok(kek) => {
            trace.real_argon2id_ops += 1;
            kek
        }
        Err(err) => {
            dummy_unwrap_slot0_traced(&payload.params, vault_aad, trace);
            return Err(VaultError::Crypto(err));
        }
    };

    trace.real_aead_ops += 1;
    unwrap_dek_with_kek(
        &mut kek,
        &payload.nonce,
        &aad,
        &payload.ciphertext,
        &payload.auth_tag,
    )
}

/// Slot 1 / Slot 2 エントリの復号を試行し、不在・無効・フォーマット不正・入力長不足時はダミー暗号演算で補完する。
fn eval_hkdf_slot_or_dummy(
    spec: &HkdfSlotSpec,
    entry: Option<&KekSlotEntry>,
    is_slot_valid: bool,
    ikm: &[u8],
    vault_aad: &[u8],
    trace: &mut SlotEvalTrace,
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    if !is_slot_valid {
        dummy_unwrap_hkdf_slot_traced(spec, vault_aad, trace);
        return Err(VaultError::AuthenticationFailed);
    }

    let Some(slot_entry) = entry else {
        dummy_unwrap_hkdf_slot_traced(spec, vault_aad, trace);
        return Err(VaultError::SlotNotFound);
    };

    let fields = match HkdfSlotFields::from_slot_entry(slot_entry, spec) {
        Ok(fields) => fields,
        Err(err) => {
            dummy_unwrap_hkdf_slot_traced(spec, vault_aad, trace);
            return Err(err);
        }
    };

    if ikm.len() < spec.min_secret_len {
        dummy_unwrap_hkdf_slot_traced(spec, vault_aad, trace);
        return Err(VaultError::Crypto(CryptoError::InvalidKeySize));
    }

    let aad = match build_hkdf_slot_aad(spec, &fields.salt, vault_aad) {
        Ok(aad) => aad,
        Err(err) => {
            dummy_unwrap_hkdf_slot_traced(spec, vault_aad, trace);
            return Err(VaultError::Crypto(err));
        }
    };

    let mut kek = match hkdf_sha256_derive_32(&fields.salt, ikm, spec.hkdf_info) {
        Ok(kek) => {
            trace.real_hkdf_ops += 1;
            kek
        }
        Err(err) => {
            dummy_unwrap_hkdf_slot_traced(spec, vault_aad, trace);
            return Err(VaultError::Crypto(err));
        }
    };

    trace.real_aead_ops += 1;
    unwrap_dek_with_kek(
        &mut kek,
        &fields.nonce,
        &aad,
        &fields.ciphertext,
        &fields.auth_tag,
    )
}

/// Slot 2 (整形済みリカバリーコード) の正準化と復号を試行し、失敗時もダミー暗号演算で補完する。
fn eval_slot2_code_or_dummy(
    entry: Option<&KekSlotEntry>,
    is_slot_valid: bool,
    recovery_code: &[u8],
    vault_aad: &[u8],
    trace: &mut SlotEvalTrace,
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    if !is_slot_valid {
        dummy_unwrap_slot2_code_traced(vault_aad, trace);
        return Err(VaultError::AuthenticationFailed);
    }

    let mut normalized = match normalize_recovery_code(recovery_code) {
        Ok(norm) => norm,
        Err(err) => {
            dummy_unwrap_slot2_code_traced(vault_aad, trace);
            return Err(err);
        }
    };

    let res = eval_hkdf_slot_or_dummy(
        &SLOT2_SPEC,
        entry,
        is_slot_valid,
        normalized.as_slice(),
        vault_aad,
        trace,
    );
    volatile_zeroize(normalized.as_mut_slice());
    res
}

/// 単一エントリと提示された資格情報を評価して DEK 復号を試行し、無効時やエラー時もダミー暗号演算を保証する。
fn eval_entry_credential_traced(
    entry: Option<&KekSlotEntry>,
    slot_valid: bool,
    credential: SlotCredential<'_>,
    vault_aad: &[u8],
    fallback_params: &Argon2Params,
    trace: &mut SlotEvalTrace,
) -> Result<SecretBytes<DEK_LEN>, VaultError> {
    match credential {
        SlotCredential::Password { password, secret } => eval_slot0_or_dummy(
            entry,
            slot_valid,
            password,
            secret,
            vault_aad,
            fallback_params,
            trace,
        ),
        SlotCredential::Prf(prf_secret) => {
            eval_hkdf_slot_or_dummy(&SLOT1_SPEC, entry, slot_valid, prf_secret, vault_aad, trace)
        }
        SlotCredential::Recovery(recovery_secret) => eval_hkdf_slot_or_dummy(
            &SLOT2_SPEC,
            entry,
            slot_valid,
            recovery_secret,
            vault_aad,
            trace,
        ),
        SlotCredential::RecoveryCode(recovery_code) => {
            eval_slot2_code_or_dummy(entry, slot_valid, recovery_code, vault_aad, trace)
        }
    }
}

/// スロットエントリ一覧から Slot 0 の有効な [`Argon2Params`] を抽出し、取得不能時はフォールバックを返す。
fn resolve_slot_entries_slot0_argon2_params(
    entries: &[KekSlotEntry],
    fallback: &Argon2Params,
) -> Argon2Params {
    if let Ok(entry) = find_slot_entry(entries, SLOT_ID_ARGON2ID)
        && let Ok(payload) = Argon2idSlotPayload::from_slot_entry(entry)
    {
        return payload.params;
    }
    resolve_valid_argon2_params(fallback)
}

/// Vault 内から Slot 0 の有効な [`Argon2Params`] を抽出し、取得不能時はフォールバックを返す。
#[inline]
fn resolve_vault_slot0_argon2_params(vault: &Vault, fallback: &Argon2Params) -> Argon2Params {
    resolve_slot_entries_slot0_argon2_params(&vault.slots, fallback)
}

impl VaultEngine {
    /// TLV の [`KekSlotEntry`] 一覧を検証し、施錠状態の新しい [`VaultEngine`] を生成する。
    ///
    /// エントリ群の中に有効な Slot 0 (Argon2id) が存在する場合はその [`Argon2Params`] をダミー演算用に初期設定し、
    /// 不在または破損時はターゲット環境のデフォルトパラメータを採用する。
    #[must_use]
    pub fn from_slot_entries(entries: &[KekSlotEntry]) -> Self {
        let dummy_argon2_params =
            resolve_slot_entries_slot0_argon2_params(entries, &Argon2Params::default_for_target());
        Self::new(inspect_kek_slots(entries)).with_dummy_argon2_params(dummy_argon2_params)
    }

    /// 指定スロットの FSM 遷移 (`Locked -> Unlocking -> Unlocked` / `Locked`) と復号を共通実行する内部ヘルパー。
    ///
    /// 外部公開API境界におけるオラクル排除のため、内部詳細エラーは [`VaultError::mask_auth_error`] により
    /// 単一の [`VaultError::AuthenticationFailed`] へ一様マスキングする。
    fn unlock_with_slot_fn<F>(&mut self, kind: SlotKind, unwrap_fn: F) -> Result<(), VaultError>
    where
        F: FnOnce(&Argon2Params, bool) -> Result<SecretBytes<DEK_LEN>, VaultError>,
    {
        self.start_unlock(kind)
            .map_err(VaultError::mask_auth_error)?;

        let slot_valid = self.slots().is_kind_valid(kind);
        let fallback_params = *self.dummy_argon2_params();

        match unwrap_fn(&fallback_params, slot_valid) {
            Ok(mut dek) => {
                if let Err(err) = self.complete_unlock(kind, &mut dek) {
                    let _ = self.fail_unlock();
                    return Err(err.mask_auth_error());
                }
                Ok(())
            }
            Err(err) => {
                let _ = self.fail_unlock();
                Err(err.mask_auth_error())
            }
        }
    }

    /// 単一の [`KekSlotEntry`] と [`SlotCredential`] を用いて解錠パイプラインを実行する中核メソッド。
    ///
    /// `Locked -> Unlocking -> Unlocked` の状態遷移を厳密に制御し、
    /// スロット無効時やフォーマット不正時も含めて資格情報に応じたダミー暗号演算を実行した上で、
    /// オラクル排除のため単一の [`VaultError::AuthenticationFailed`] へ一様マスキングする。
    ///
    /// # Errors
    ///
    /// - 現在の状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - スロット無効, フォーマット不正, パラメータ不正, MAC 不一致などの認証失敗時は、
    ///   オラクル排除のため単一の [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_with_entry(
        &mut self,
        entry: &KekSlotEntry,
        credential: SlotCredential<'_>,
        vault_aad: &[u8],
    ) -> Result<(), VaultError> {
        let mut trace = SlotEvalTrace::default();
        self.unlock_with_entry_traced(entry, credential, vault_aad, &mut trace)
    }

    /// [`SlotEvalTrace`] 付きで単一エントリ解錠を実行する内部実装。
    fn unlock_with_entry_traced(
        &mut self,
        entry: &KekSlotEntry,
        credential: SlotCredential<'_>,
        vault_aad: &[u8],
        trace: &mut SlotEvalTrace,
    ) -> Result<(), VaultError> {
        let kind = credential.slot_kind();
        self.unlock_with_slot_fn(kind, |fallback_params, slot_valid| {
            eval_entry_credential_traced(
                Some(entry),
                slot_valid,
                credential,
                vault_aad,
                fallback_params,
                trace,
            )
        })
    }

    /// Slot 0 (Argon2id マスターパスワード) エントリを用いて解錠パイプラインを実行する。
    ///
    /// 内部で [`Self::unlock_with_entry`] に処理を委譲する。
    ///
    /// # 前提条件
    ///
    /// 現在の状態が [`crate::envelope::VaultState::Locked`] であり、
    /// かつ本エンジン上で Slot 0 が [`SlotStatus::Valid`] として登録されている必要がある。
    ///
    /// # Errors
    ///
    /// - 現在の状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - スロット無効, フォーマット不正, KDF パラメータ不正, MAC 不一致などの認証失敗時は、
    ///   オラクル排除のため単一の [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_with_slot0(
        &mut self,
        entry: &KekSlotEntry,
        password: &[u8],
        vault_aad: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_with_entry(entry, SlotCredential::password(password), vault_aad)
    }

    /// ペッパー (`secret`) を併用し、Slot 0 エントリによる解錠パイプラインを実行する。
    ///
    /// 内部で [`Self::unlock_with_entry`] に処理を委譲する。
    ///
    /// # Errors
    ///
    /// [`Self::unlock_with_slot0`] と同じエラー条件に従う。
    pub fn unlock_with_slot0_with_secret(
        &mut self,
        entry: &KekSlotEntry,
        password: &[u8],
        secret: &[u8],
        vault_aad: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_with_entry(
            entry,
            SlotCredential::password_with_secret(password, secret),
            vault_aad,
        )
    }

    #[cfg(test)]
    fn unlock_with_slot0_with_secret_traced(
        &mut self,
        entry: &KekSlotEntry,
        password: &[u8],
        secret: &[u8],
        vault_aad: &[u8],
        trace: &mut SlotEvalTrace,
    ) -> Result<(), VaultError> {
        self.unlock_with_entry_traced(
            entry,
            SlotCredential::password_with_secret(password, secret),
            vault_aad,
            trace,
        )
    }

    /// Slot 1 (WebAuthn PRF / HKDF-SHA256) エントリを用いて解錠パイプラインを実行する。
    ///
    /// 内部で [`Self::unlock_with_entry`] に処理を委譲する。
    ///
    /// # Errors
    ///
    /// - 現在の状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - スロット無効, フォーマット不正, PRF 長不足, MAC 不一致などの認証失敗時は、
    ///   オラクル排除のため単一の [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_with_slot1(
        &mut self,
        entry: &KekSlotEntry,
        prf_secret: &[u8],
        vault_aad: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_with_entry(entry, SlotCredential::prf(prf_secret), vault_aad)
    }

    #[cfg(test)]
    fn unlock_with_slot1_traced(
        &mut self,
        entry: &KekSlotEntry,
        prf_secret: &[u8],
        vault_aad: &[u8],
        trace: &mut SlotEvalTrace,
    ) -> Result<(), VaultError> {
        self.unlock_with_entry_traced(entry, SlotCredential::prf(prf_secret), vault_aad, trace)
    }

    /// Slot 2 (生リカバリーシークレット) エントリを用いて解錠パイプラインを実行する。
    ///
    /// 内部で [`Self::unlock_with_entry`] に処理を委譲する。
    ///
    /// # Errors
    ///
    /// - 現在の状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - スロット無効, フォーマット不正, シークレット長不足, MAC 不一致などの認証失敗時は、
    ///   オラクル排除のため単一の [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_with_slot2(
        &mut self,
        entry: &KekSlotEntry,
        recovery_secret: &[u8],
        vault_aad: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_with_entry(entry, SlotCredential::recovery(recovery_secret), vault_aad)
    }

    #[cfg(test)]
    #[allow(dead_code)]
    fn unlock_with_slot2_traced(
        &mut self,
        entry: &KekSlotEntry,
        recovery_secret: &[u8],
        vault_aad: &[u8],
        trace: &mut SlotEvalTrace,
    ) -> Result<(), VaultError> {
        self.unlock_with_entry_traced(
            entry,
            SlotCredential::recovery(recovery_secret),
            vault_aad,
            trace,
        )
    }

    /// Slot 2 (整形済み英数字リカバリーコード) エントリを用いて解錠パイプラインを実行する。
    ///
    /// 内部で [`Self::unlock_with_entry`] に処理を委譲する。
    ///
    /// # Errors
    ///
    /// [`Self::unlock_with_slot2`] と同じく、状態不正時は [`VaultError::InvalidState`] を返し、
    /// リカバリーコード正準化失敗を含むその他の認証失敗はすべて [`VaultError::AuthenticationFailed`] を返す。
    pub fn unlock_with_slot2_code(
        &mut self,
        entry: &KekSlotEntry,
        recovery_code: &[u8],
        vault_aad: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_with_entry(
            entry,
            SlotCredential::recovery_code(recovery_code),
            vault_aad,
        )
    }

    #[cfg(test)]
    fn unlock_with_slot2_code_traced(
        &mut self,
        entry: &KekSlotEntry,
        recovery_code: &[u8],
        vault_aad: &[u8],
        trace: &mut SlotEvalTrace,
    ) -> Result<(), VaultError> {
        self.unlock_with_entry_traced(
            entry,
            SlotCredential::recovery_code(recovery_code),
            vault_aad,
            trace,
        )
    }

    /// [`Vault`] コンテナ全体から Slot 0 を検索し、Vault ヘッダー AAD をバインドして解錠する。
    ///
    /// # Errors
    ///
    /// - 状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - スロット不在, 重複, フォーマット不正, MAC 不一致を含むすべての認証失敗は、
    ///   オラクル排除のため [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_vault_with_password(
        &mut self,
        vault: &Vault,
        password: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_vault_with_credential(vault, SlotCredential::password(password))
    }

    /// [`Vault`] コンテナ全体から Slot 1 (WebAuthn PRF) を検索し、Vault ヘッダー AAD をバインドして解錠する。
    ///
    /// # Errors
    ///
    /// - 状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - スロット不在, 重複, フォーマット不正, PRF 長不足, MAC 不一致を含むすべての認証失敗は、
    ///   オラクル排除のため [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_vault_with_prf(
        &mut self,
        vault: &Vault,
        prf_secret: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_vault_with_credential(vault, SlotCredential::prf(prf_secret))
    }

    /// [`Vault`] コンテナ全体から Slot 2 (生リカバリーシークレット) を検索し、
    /// Vault ヘッダー AAD をバインドして解錠する。
    ///
    /// # Errors
    ///
    /// - 状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - スロット不在, 重複, フォーマット不正, シークレット長不足, MAC 不一致を含むすべての認証失敗は、
    ///   オラクル排除のため [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_vault_with_recovery(
        &mut self,
        vault: &Vault,
        recovery_secret: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_vault_with_credential(vault, SlotCredential::recovery(recovery_secret))
    }

    /// [`Vault`] コンテナ全体から Slot 2 (整形済みリカバリーコード) を検索し、
    /// Vault ヘッダー AAD をバインドして解錠する。
    ///
    /// # Errors
    ///
    /// [`Self::unlock_vault_with_recovery`] と同じく、状態不正時は [`VaultError::InvalidState`] を返し、
    /// リカバリーコード正準化失敗を含むその他の認証失敗はすべて [`VaultError::AuthenticationFailed`] を返す。
    pub fn unlock_vault_with_recovery_code(
        &mut self,
        vault: &Vault,
        recovery_code: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_vault_with_credential(vault, SlotCredential::recovery_code(recovery_code))
    }

    /// 残余スロット向け: 指定された [`SlotKind`] に対応するダミー暗号演算を 1 回実行する。
    fn run_dummy_for_slot_kind_traced(
        &self,
        vault: &Vault,
        kind: SlotKind,
        header_aad: &[u8],
        trace: &mut SlotEvalTrace,
    ) {
        match kind {
            SlotKind::Argon2id => {
                let params = resolve_vault_slot0_argon2_params(vault, self.dummy_argon2_params());
                dummy_unwrap_slot0_traced(&params, header_aad, trace);
            }
            SlotKind::Prf => dummy_unwrap_hkdf_slot_traced(&SLOT1_SPEC, header_aad, trace),
            SlotKind::Recovery => dummy_unwrap_hkdf_slot_traced(&SLOT2_SPEC, header_aad, trace),
        }
    }

    /// 先行スロット成功後の残余資格情報に対してダミー暗号演算を 1 回実行する。
    fn run_dummy_for_credential_traced(
        &self,
        vault: &Vault,
        credential: SlotCredential<'_>,
        header_aad: &[u8],
        trace: &mut SlotEvalTrace,
    ) {
        match credential {
            SlotCredential::Password { .. } => {
                self.run_dummy_for_slot_kind_traced(vault, SlotKind::Argon2id, header_aad, trace);
            }
            SlotCredential::Prf(_) => {
                dummy_unwrap_hkdf_slot_traced(&SLOT1_SPEC, header_aad, trace);
            }
            SlotCredential::Recovery(_) => {
                dummy_unwrap_hkdf_slot_traced(&SLOT2_SPEC, header_aad, trace);
            }
            SlotCredential::RecoveryCode(_) => {
                dummy_unwrap_slot2_code_traced(header_aad, trace);
            }
        }
    }

    /// [`Vault`] 内の指定資格情報スロットを評価して DEK 復号を試行し、不在・重複・無効時もダミー暗号演算を保証する。
    fn eval_vault_credential_traced(
        &self,
        vault: &Vault,
        credential: SlotCredential<'_>,
        header_aad: &[u8],
        trace: &mut SlotEvalTrace,
    ) -> Result<SecretBytes<DEK_LEN>, VaultError> {
        let slot_id = credential.slot_kind().as_slot_id();
        let slot_valid = self.slots().is_slot_valid(slot_id);
        let entry = match find_slot_entry(&vault.slots, slot_id) {
            Ok(found) => found,
            Err(find_err) => {
                self.run_dummy_for_credential_traced(vault, credential, header_aad, trace);
                return Err(find_err);
            }
        };

        let dummy_argon2_params =
            resolve_vault_slot0_argon2_params(vault, self.dummy_argon2_params());
        eval_entry_credential_traced(
            Some(entry),
            slot_valid,
            credential,
            header_aad,
            &dummy_argon2_params,
            trace,
        )
    }

    /// 指定された単一の [`SlotCredential`] に対応するスロットを [`Vault`] から検索して解錠する。
    ///
    /// 対象スロットの不在, 重複, 破損, 入力長不正のいずれで失敗する場合でも、
    /// 当該スロット種別と同等コストのダミー暗号演算を実行し、特定スロットの有無に伴うタイミング漏洩を抑制する。
    ///
    /// # Errors
    ///
    /// - 状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - スロット不在, 重複, フォーマット不正, 入力長/形式不正, MAC 不一致を含むすべての認証失敗は、
    ///   オラクル排除のため単一の [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_vault_with_credential(
        &mut self,
        vault: &Vault,
        credential: SlotCredential<'_>,
    ) -> Result<(), VaultError> {
        let mut trace = SlotEvalTrace::default();
        self.unlock_vault_with_credential_traced(vault, credential, &mut trace)
    }

    /// [`SlotEvalTrace`] 付きで単一資格情報解錠を実行する内部実装。
    fn unlock_vault_with_credential_traced(
        &mut self,
        vault: &Vault,
        credential: SlotCredential<'_>,
        trace: &mut SlotEvalTrace,
    ) -> Result<(), VaultError> {
        let kind = credential.slot_kind();
        self.start_unlock(kind)
            .map_err(VaultError::mask_auth_error)?;

        let header_aad = vault.header.associated_data();
        match self.eval_vault_credential_traced(vault, credential, &header_aad, trace) {
            Ok(mut dek) => {
                if let Err(err) = self.complete_unlock(kind, &mut dek) {
                    let _ = self.fail_unlock();
                    return Err(err.mask_auth_error());
                }
                Ok(())
            }
            Err(err) => {
                let _ = self.fail_unlock();
                Err(err.mask_auth_error())
            }
        }
    }

    /// 多重化解錠および残余ダミー演算を実行し、処理結果と [`SlotEvalTrace`] を返す内部コア。
    fn unlock_vault_with_any_traced(
        &mut self,
        vault: &Vault,
        credentials: &[SlotCredential<'_>],
        include_missing_slot_kinds: bool,
    ) -> (Result<SlotKind, VaultError>, SlotEvalTrace) {
        let mut trace = SlotEvalTrace::default();
        if !self.state().is_locked() {
            return (Err(VaultError::InvalidState), trace);
        }
        if credentials.is_empty() && !include_missing_slot_kinds {
            return (Err(VaultError::AuthenticationFailed), trace);
        }

        let start_kind = credentials
            .first()
            .map_or(SlotKind::Argon2id, |cred| cred.slot_kind());
        if let Err(err) = self.start_unlock(start_kind) {
            return (Err(err.mask_auth_error()), trace);
        }

        let header_aad = vault.header.associated_data();
        let mut matched: Option<(SlotKind, SecretBytes<DEK_LEN>)> = None;
        let mut seen_kinds = [false; SlotKind::COUNT];

        // 先行スロットの成否や対象スロットの有無に関わらず、全候補に対して実演算またはダミー演算を1回実行する。
        // 同一 SlotKind の複数候補(旧・新パスワード等)も順次評価し、後続の正しい候補による解錠を保証する。
        for &credential in credentials {
            let kind_idx = credential.slot_kind().as_slot_id() as usize;
            seen_kinds[kind_idx] = true;
            if matched.is_some() {
                self.run_dummy_for_credential_traced(vault, credential, &header_aad, &mut trace);
            } else if let Ok(dek) =
                self.eval_vault_credential_traced(vault, credential, &header_aad, &mut trace)
            {
                matched = Some((credential.slot_kind(), dek));
            }
        }

        // 全スロット平滑化モードでは、未提示のスロット種別にもダミー暗号演算を補完する。
        if include_missing_slot_kinds {
            for kind in [SlotKind::Argon2id, SlotKind::Prf, SlotKind::Recovery] {
                if !seen_kinds[kind.as_slot_id() as usize] {
                    self.run_dummy_for_slot_kind_traced(vault, kind, &header_aad, &mut trace);
                }
            }
        }

        match matched {
            Some((kind, mut dek)) => match self.complete_unlock(kind, &mut dek) {
                Ok(()) => (Ok(kind), trace),
                Err(err) => {
                    let _ = self.fail_unlock();
                    (Err(err.mask_auth_error()), trace)
                }
            },
            None => {
                let _ = self.fail_unlock();
                (Err(VaultError::AuthenticationFailed), trace)
            }
        }
    }

    /// 提示された複数の [`SlotCredential`] を順次評価し、いずれか 1 スロットで解錠可能な多重化解錠を実行する。
    ///
    /// 先行スロットが認証成功した場合であっても早期リターンせず、
    /// 残余の資格情報に対応するスロットへダミー暗号演算 (KDF + AEAD 復号) を実行して実行時間を平滑化する。
    /// また、先行スロットが未設定, 破損, 重複, 認証失敗のいずれであっても同種別のダミー演算を挟みつつ、
    /// 後続スロットの試行を継続し、全候補完了後に最初に成功した DEK で `Unlocked` へ遷移する。
    /// `EnvelopeFsm.v` の `slot_multiplexing_soundness` 定理に対応する実行時パイプライン。
    ///
    /// # Errors
    ///
    /// - 状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - `credentials` が空の場合や、すべての資格情報で解錠に失敗した場合は、
    ///   オラクル排除のため単一の [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_vault_with_any(
        &mut self,
        vault: &Vault,
        credentials: &[SlotCredential<'_>],
    ) -> Result<SlotKind, VaultError> {
        let (result, _) = self.unlock_vault_with_any_traced(vault, credentials, false);
        result
    }

    /// 提示された資格情報リストに加え、未提示のスロット種別 (Slot 0 / 1 / 2) にもダミー暗号演算を実行し、
    /// 常に全 3 スロット種別分の演算コストで解錠を評価する完全平滑化解錠を実行する。
    ///
    /// 提示された `credentials` が特定スロットのみを含む場合でも、
    /// Vault 内の他スロット構成や認証成功スロットの種別に伴う実行時間差を隠蔽したい場合に使用する。
    /// 同一 [`SlotKind`] の資格情報が複数提示された場合(旧・新パスワード候補など)もすべての候補を順次評価(またはダミー演算)し、
    /// さらに未提示のスロット種別に対するダミー暗号演算を補完して実行時間を平滑化する。
    ///
    /// # Errors
    ///
    /// - 状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - `credentials` が空の場合や、すべての資格情報で解錠に失敗した場合は、
    ///   オラクル排除のため単一の [`VaultError::AuthenticationFailed`] へ一様マスキングして返す。
    pub fn unlock_vault_with_all_slots(
        &mut self,
        vault: &Vault,
        credentials: &[SlotCredential<'_>],
    ) -> Result<SlotKind, VaultError> {
        let (result, _) = self.unlock_vault_with_any_traced(vault, credentials, true);
        result
    }

    /// 解錠状態の DEK を用いて新しい Slot 0 (Argon2id) エントリを生成する。
    ///
    /// 初期パスワード設定やマスターパスワード変更時のスロット再生成に使用する。
    ///
    /// # Errors
    ///
    /// - 現在の状態が [`crate::envelope::VaultState::Unlocked`] でない場合は [`VaultError::InvalidState`] を返す。
    /// - ラップ処理に失敗した場合は対応する [`VaultError`] を返す。
    pub fn wrap_slot0(
        &self,
        password: &[u8],
        salt: &[u8; SLOT0_SALT_LEN],
        nonce: &[u8; SLOT0_NONCE_LEN],
        params: &Argon2Params,
        vault_aad: &[u8],
    ) -> Result<KekSlotEntry, VaultError> {
        self.wrap_slot0_with_secret(password, salt, nonce, params, &[], vault_aad)
    }

    /// ペッパー (`secret`) を併用し、解錠状態の DEK から新しい Slot 0 エントリを生成する。
    ///
    /// # Errors
    ///
    /// [`Self::wrap_slot0`] と同じエラー条件に従う。
    pub fn wrap_slot0_with_secret(
        &self,
        password: &[u8],
        salt: &[u8; SLOT0_SALT_LEN],
        nonce: &[u8; SLOT0_NONCE_LEN],
        params: &Argon2Params,
        secret: &[u8],
        vault_aad: &[u8],
    ) -> Result<KekSlotEntry, VaultError> {
        let dek = self.dek()?;
        wrap_dek_slot0_with_secret(dek, password, salt, nonce, params, secret, vault_aad)
    }

    /// 解錠状態の DEK を用いて新しい Slot 1 (WebAuthn PRF / HKDF-SHA256) エントリを生成する。
    ///
    /// # Errors
    ///
    /// - 現在の状態が [`crate::envelope::VaultState::Unlocked`] でない場合は [`VaultError::InvalidState`] を返す。
    /// - ラップ処理に失敗した場合は対応する [`VaultError`] を返す。
    pub fn wrap_slot1(
        &self,
        prf_secret: &[u8],
        salt: &[u8; SLOT1_SALT_LEN],
        nonce: &[u8; SLOT1_NONCE_LEN],
        vault_aad: &[u8],
    ) -> Result<KekSlotEntry, VaultError> {
        let dek = self.dek()?;
        wrap_dek_slot1(dek, prf_secret, salt, nonce, vault_aad)
    }

    /// 解錠状態の DEK を用いて新しい Slot 2 (生リカバリーシークレット) エントリを生成する。
    ///
    /// # Errors
    ///
    /// - 現在の状態が [`crate::envelope::VaultState::Unlocked`] でない場合は [`VaultError::InvalidState`] を返す。
    /// - ラップ処理に失敗した場合は対応する [`VaultError`] を返す。
    pub fn wrap_slot2(
        &self,
        recovery_secret: &[u8],
        salt: &[u8; SLOT2_SALT_LEN],
        nonce: &[u8; SLOT2_NONCE_LEN],
        vault_aad: &[u8],
    ) -> Result<KekSlotEntry, VaultError> {
        let dek = self.dek()?;
        wrap_dek_slot2(dek, recovery_secret, salt, nonce, vault_aad)
    }

    /// 解錠状態の DEK を用いて新しい Slot 2 (整形済み英数字リカバリーコード) エントリを生成する。
    ///
    /// # Errors
    ///
    /// - 現在の状態が [`crate::envelope::VaultState::Unlocked`] でない場合は [`VaultError::InvalidState`] を返す。
    /// - コード正準化またはラップ処理に失敗した場合は対応する [`VaultError`] を返す。
    pub fn wrap_slot2_code(
        &self,
        recovery_code: &[u8],
        salt: &[u8; SLOT2_SALT_LEN],
        nonce: &[u8; SLOT2_NONCE_LEN],
        vault_aad: &[u8],
    ) -> Result<KekSlotEntry, VaultError> {
        let dek = self.dek()?;
        wrap_dek_slot2_code(dek, recovery_code, salt, nonce, vault_aad)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::envelope::{SLOT_ID_PRF, SLOT_ID_RECOVERY, VaultState};
    use crate::tlv::{EntryPayload, TlvRecord, VAULT_MAGIC, deserialize, serialize};
    use alloc::{format, vec};
    use proptest::prelude::*;

    fn test_params() -> Argon2Params {
        Argon2Params::fast_test()
    }

    fn test_dek() -> SecretBytes<DEK_LEN> {
        let mut raw = [0u8; DEK_LEN];
        for (idx, byte) in raw.iter_mut().enumerate() {
            *byte = (idx as u8).wrapping_mul(7).wrapping_add(0x11);
        }
        SecretBytes::new(raw)
    }

    fn test_salt() -> [u8; SLOT0_SALT_LEN] {
        *b"fidelogic-salt01"
    }

    fn test_nonce() -> [u8; SLOT0_NONCE_LEN] {
        *b"fidelogic-xchacha-nonce!"
    }

    fn test_header() -> VaultHeader {
        VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: CipherSuiteId::XChaCha20Poly1305.as_u8(),
            epoch_id: 42,
        }
    }

    #[test]
    fn test_kdf_kind_conversions() {
        assert_eq!(KdfKind::from_u8(KDF_KIND_ARGON2ID), Ok(KdfKind::Argon2id));
        assert_eq!(
            KdfKind::from_u8(KDF_KIND_HKDF_SHA256),
            Ok(KdfKind::HkdfSha256)
        );
        assert_eq!(KdfKind::from_u8(KDF_KIND_RECOVERY), Ok(KdfKind::Recovery));
        assert_eq!(KdfKind::from_u8(0), Err(TlvParseError::UnsupportedSuite));
        assert_eq!(KdfKind::try_from(255), Err(TlvParseError::UnsupportedSuite));
        assert_eq!(u8::from(KdfKind::Argon2id), 1);
    }

    #[test]
    fn test_slot0_wrap_and_unwrap_roundtrip() {
        let dek = test_dek();
        let password = b"correct-horse-battery-staple";
        let salt = test_salt();
        let nonce = test_nonce();
        let params = test_params();
        let header = test_header();

        let entry =
            wrap_dek_slot0_for_header(&dek, password, &salt, &nonce, &params, &header).unwrap();
        assert_eq!(entry.slot_id(), SLOT_ID_ARGON2ID);
        assert_eq!(entry.kdf_kind(), KDF_KIND_ARGON2ID);
        assert_eq!(
            entry.wrapped_dek().len(),
            SLOT0_WRAPPED_DEK_LEN,
            "Slot 0 ラップ済み DEK 長が 100 バイトであることの確認に成功。"
        );
        assert!(is_valid_slot0_entry(&entry));

        let unwrapped = unwrap_dek_slot0_for_header(&entry, password, &header).unwrap();
        assert_eq!(
            unwrapped.as_bytes(),
            dek.as_bytes(),
            "Slot 0 復号 DEK と元 DEK の一致確認に成功。"
        );
    }

    #[test]
    fn test_slot0_wrap_and_unwrap_with_secret_pepper() {
        let dek = test_dek();
        let password = b"user-master-password";
        let pepper = b"app-secret-pepper-v1";
        let salt = test_salt();
        let nonce = test_nonce();
        let params = test_params();
        let aad = test_header().associated_data();

        let entry =
            wrap_dek_slot0_with_secret(&dek, password, &salt, &nonce, &params, pepper, &aad)
                .unwrap();

        let ok_dek = unwrap_dek_slot0_with_secret(&entry, password, pepper, &aad).unwrap();
        assert_eq!(ok_dek.as_bytes(), dek.as_bytes());

        // ペッパーの未指定または不一致時に復号が失敗することを確認。
        assert_eq!(
            unwrap_dek_slot0(&entry, password, &aad).err(),
            Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
        );
        assert_eq!(
            unwrap_dek_slot0_with_secret(&entry, password, b"wrong-pepper", &aad).err(),
            Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
        );
    }

    #[test]
    fn test_slot0_wrong_password_and_tamper_detection() {
        let dek = test_dek();
        let password = b"my-strong-password";
        let salt = test_salt();
        let nonce = test_nonce();
        let params = test_params();
        let header = test_header();
        let aad = header.associated_data();

        let entry = wrap_dek_slot0(&dek, password, &salt, &nonce, &params, &aad).unwrap();

        // 誤パスワードの拒絶。
        assert_eq!(
            unwrap_dek_slot0(&entry, b"wrong-password", &aad).err(),
            Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed)),
            "誤パスワードに対するAEAD復号失敗の確認に成功。"
        );

        // VaultHeader (epoch_id 巻き戻し) の改ざん検知。
        let rolled_back = VaultHeader {
            epoch_id: 41,
            ..header
        };
        assert_eq!(
            unwrap_dek_slot0_for_header(&entry, password, &rolled_back).err(),
            Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed)),
            "epoch_id 巻き戻し時のAAD不一致検知に成功。"
        );

        // wrapped_dek 内 (salt, nonce, ciphertext, auth_tag) の全バイト位置に対する改ざん検知。
        // 先頭 12 バイトは Argon2id パラメータのため、パラメータ制約に違反するか AEAD タグ不一致となる。
        for pos in 0..SLOT0_WRAPPED_DEK_LEN {
            let mut tampered = entry.wrapped_dek().to_vec();
            tampered[pos] ^= 0x01;
            let tampered_entry =
                KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, tampered).unwrap();
            let res = unwrap_dek_slot0(&tampered_entry, password, &aad);
            assert!(res.is_err(), "バイト位置 {pos} の1ビット改ざん検知に成功。");
        }
    }

    #[test]
    fn test_slot0_rejects_invalid_headers_lengths_and_params() {
        let dek = test_dek();
        let password = b"pw";
        let salt = test_salt();
        let nonce = test_nonce();
        let params = test_params();
        let aad = test_header().associated_data();

        let entry = wrap_dek_slot0(&dek, password, &salt, &nonce, &params, &aad).unwrap();

        // slot_id 不一致。
        let wrong_slot =
            KekSlotEntry::new(SLOT_ID_PRF, KDF_KIND_ARGON2ID, entry.wrapped_dek().to_vec())
                .unwrap();
        assert_eq!(
            unwrap_dek_slot0(&wrong_slot, password, &aad).err(),
            Some(VaultError::Parse(TlvParseError::InvalidFormat))
        );

        // kdf_kind 不一致。
        let wrong_kdf = KekSlotEntry::new(
            SLOT_ID_ARGON2ID,
            KDF_KIND_HKDF_SHA256,
            entry.wrapped_dek().to_vec(),
        )
        .unwrap();
        assert_eq!(
            unwrap_dek_slot0(&wrong_kdf, password, &aad).err(),
            Some(VaultError::Parse(TlvParseError::InvalidFormat))
        );

        // 長さ不足および長さ超過。
        for invalid_len in [0, 12, 99, 101] {
            let bad = KekSlotEntry::new(
                SLOT_ID_ARGON2ID,
                KDF_KIND_ARGON2ID,
                alloc::vec![0u8; invalid_len],
            )
            .unwrap();
            assert_eq!(
                unwrap_dek_slot0(&bad, password, &aad).err(),
                Some(VaultError::Parse(TlvParseError::InvalidLength))
            );
        }

        // 不正パラメータ (p_cost=0, m_cost < 8*p_cost, 上限超過 m_cost) の事前拒絶。
        let mut bad_m = entry.wrapped_dek().to_vec();
        bad_m[0..4].copy_from_slice(&(MAX_SLOT0_M_COST + 1).to_be_bytes());
        let bad_m_entry = KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, bad_m).unwrap();
        assert_eq!(
            unwrap_dek_slot0(&bad_m_entry, password, &aad).err(),
            Some(VaultError::Crypto(CryptoError::InvalidParameter))
        );

        let mut zero_p = entry.wrapped_dek().to_vec();
        zero_p[8..12].copy_from_slice(&0u32.to_be_bytes());
        let zero_p_entry = KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, zero_p).unwrap();
        assert_eq!(
            unwrap_dek_slot0(&zero_p_entry, password, &aad).err(),
            Some(VaultError::Crypto(CryptoError::InvalidParameter))
        );

        // ラップ時の不正 output_len 拒絶。
        let bad_out_len = Argon2Params::fast_test().with_output_len(16);
        assert_eq!(
            wrap_dek_slot0(&dek, password, &salt, &nonce, &bad_out_len, &aad).err(),
            Some(VaultError::Crypto(CryptoError::InvalidKeySize))
        );
    }

    #[test]
    fn test_vault_engine_slot0_unlock_lock_rewrap_and_e2e_tlv() {
        let dek = test_dek();
        let password_v1 = b"initial-master-password";
        let password_v2 = b"rotated-master-password";
        let salt1 = test_salt();
        let nonce1 = test_nonce();
        let params = test_params();
        let header = test_header();
        let aad = header.associated_data();

        let slot0_v1 = wrap_dek_slot0(&dek, password_v1, &salt1, &nonce1, &params, &aad).unwrap();
        let vault = Vault::new(
            header,
            alloc::vec![slot0_v1.clone()],
            alloc::vec![TlvRecord::Entry(EntryPayload::new(
                alloc::vec![1, 2, 3, 4],
                [0xAAu8; 16]
            ))],
        );

        let raw_vault = serialize(&vault).unwrap();
        let (parsed_vault, rest) = deserialize(&raw_vault).unwrap();
        assert!(rest.is_empty());

        let mut engine = VaultEngine::from_slot_entries(&parsed_vault.slots);
        assert_eq!(engine.state(), VaultState::Locked);
        assert_eq!(engine.slots().status(SLOT_ID_ARGON2ID), SlotStatus::Valid);
        assert_eq!(engine.slots().status(SLOT_ID_PRF), SlotStatus::Unset);
        assert_eq!(engine.slots().status(SLOT_ID_RECOVERY), SlotStatus::Unset);

        // 誤パスワードでの失敗時は Unlocking -> Locked に復帰し SafeState を維持しつつ、
        // 外部境界オラクル排除のため単一の AuthenticationFailed を返す。
        assert_eq!(
            engine.unlock_vault_with_password(&parsed_vault, b"wrong-pass"),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(engine.state(), VaultState::Locked);
        assert!(engine.is_safe_state());
        assert!(engine.observe_dek().is_none());

        // 正しいパスワードで解錠成功。
        assert_eq!(
            engine.unlock_vault_with_password(&parsed_vault, password_v1),
            Ok(())
        );
        assert_eq!(engine.state(), VaultState::Unlocked);
        assert!(engine.is_safe_state());
        assert_eq!(
            engine.observe_dek().map(SecretBytes::as_bytes),
            Some(dek.as_bytes())
        );

        // Unlocked 状態から再解錠を試みても InvalidState で拒絶される。
        assert_eq!(
            engine.unlock_vault_with_password(&parsed_vault, password_v1),
            Err(VaultError::InvalidState)
        );

        // 解錠状態の DEK を新パスワードで再ラップ。
        let salt2 = *b"fidelogic-salt02";
        let nonce2 = *b"fidelogic-xchacha-nonce2";
        let slot0_v2 = engine
            .wrap_slot0(password_v2, &salt2, &nonce2, &params, &aad)
            .unwrap();

        // 施錠後は wrap_slot0 の実行不可および DEK 消去済みを確認。
        engine.lock().unwrap();
        assert_eq!(engine.state(), VaultState::Locked);
        assert!(engine.observe_dek().is_none());
        assert_eq!(
            engine
                .wrap_slot0(password_v2, &salt2, &nonce2, &params, &aad)
                .err(),
            Some(VaultError::InvalidState)
        );

        // 新パスワードスロットで再解錠成功。
        assert_eq!(
            engine.unlock_with_slot0(&slot0_v2, password_v2, &aad),
            Ok(())
        );
        assert_eq!(
            engine.observe_dek().map(SecretBytes::as_bytes),
            Some(dek.as_bytes())
        );

        // Zeroized 状態からは Reset なしに解錠不可。
        engine.zeroize_key().unwrap();
        assert_eq!(engine.state(), VaultState::Zeroized);
        assert_eq!(
            engine.unlock_with_slot0(&slot0_v2, password_v2, &aad),
            Err(VaultError::InvalidState)
        );
        engine.reset().unwrap();
        assert_eq!(
            engine.unlock_with_slot0(&slot0_v2, password_v2, &aad),
            Ok(())
        );
    }

    #[test]
    fn test_inspect_kek_slots_duplicate_and_unset_handling() {
        let dek = test_dek();
        let entry = wrap_dek_slot0(
            &dek,
            b"pw",
            &test_salt(),
            &test_nonce(),
            &test_params(),
            &[],
        )
        .unwrap();

        // 正常な単一 Slot 0。
        let single = inspect_kek_slots(core::slice::from_ref(&entry));
        assert_eq!(single.argon2id, SlotStatus::Valid);

        // 重複 Slot 0 は Invalid として隔離される。
        let dup = inspect_kek_slots(&[entry.clone(), entry]);
        assert_eq!(dup.argon2id, SlotStatus::Invalid);

        // 未登録 Slot 0 の VaultEngine では正当なエントリを渡しても AuthenticationFailed。
        let mut unset_engine = VaultEngine::locked();
        let valid_entry = wrap_dek_slot0(
            &dek,
            b"pw",
            &test_salt(),
            &test_nonce(),
            &test_params(),
            &[],
        )
        .unwrap();
        assert_eq!(
            unset_engine.unlock_with_slot0(&valid_entry, b"pw", &[]),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(unset_engine.state(), VaultState::Locked);
        assert!(unset_engine.is_safe_state());
    }

    #[test]
    fn test_slot0_binary_layout_and_find_slot_entry() {
        let dek = test_dek();
        let params = Argon2Params::custom(128, 2, 1, Some(DEK_LEN)).unwrap();
        let salt = test_salt();
        let nonce = test_nonce();
        let entry = wrap_dek_slot0(&dek, b"layout-pw", &salt, &nonce, &params, b"ctx").unwrap();

        let raw = entry.wrapped_dek();
        assert_eq!(raw.len(), 100);
        assert_eq!(u32::from_be_bytes([raw[0], raw[1], raw[2], raw[3]]), 128);
        assert_eq!(u32::from_be_bytes([raw[4], raw[5], raw[6], raw[7]]), 2);
        assert_eq!(u32::from_be_bytes([raw[8], raw[9], raw[10], raw[11]]), 1);
        assert_eq!(&raw[12..28], &salt);
        assert_eq!(&raw[28..52], &nonce);

        let payload = Argon2idSlotPayload::from_slot_entry(&entry).unwrap();
        assert_eq!(payload.to_bytes(), raw);
        assert_eq!(payload.params, params);

        // find_slot_entry による検索, 不在, 重複の検知。
        let slot1 = KekSlotEntry::new(SLOT_ID_PRF, KDF_KIND_HKDF_SHA256, alloc::vec![1]).unwrap();
        let entries = [slot1, entry.clone()];
        assert_eq!(find_slot_entry(&entries, SLOT_ID_ARGON2ID), Ok(&entry));
        assert_eq!(
            find_slot_entry(&entries, SLOT_ID_RECOVERY),
            Err(VaultError::SlotNotFound)
        );

        let dup_entries = [entry.clone(), entry];
        assert_eq!(
            find_slot_entry(&dup_entries, SLOT_ID_ARGON2ID),
            Err(VaultError::Parse(TlvParseError::InvalidFormat))
        );
    }

    #[test]
    fn test_slot0_rejects_excessive_t_and_p_costs_and_insufficient_m_cost() {
        let dek = test_dek();
        let entry = wrap_dek_slot0(
            &dek,
            b"pw",
            &test_salt(),
            &test_nonce(),
            &test_params(),
            &[],
        )
        .unwrap();

        // t_cost 上限超過。
        let mut bad_t = entry.wrapped_dek().to_vec();
        bad_t[4..8].copy_from_slice(&(MAX_SLOT0_T_COST + 1).to_be_bytes());
        let bad_t_entry = KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, bad_t).unwrap();
        assert_eq!(
            unwrap_dek_slot0(&bad_t_entry, b"pw", &[]).err(),
            Some(VaultError::Crypto(CryptoError::InvalidParameter))
        );

        // p_cost 上限超過。
        let mut bad_p = entry.wrapped_dek().to_vec();
        bad_p[8..12].copy_from_slice(&(MAX_SLOT0_P_COST + 1).to_be_bytes());
        let bad_p_entry = KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, bad_p).unwrap();
        assert_eq!(
            unwrap_dek_slot0(&bad_p_entry, b"pw", &[]).err(),
            Some(VaultError::Crypto(CryptoError::InvalidParameter))
        );

        // m_cost < 8 * p_cost (p_cost = 16, m_cost = 64 < 128)。
        let mut low_m = entry.wrapped_dek().to_vec();
        low_m[8..12].copy_from_slice(&16u32.to_be_bytes());
        let low_m_entry = KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, low_m).unwrap();
        assert_eq!(
            unwrap_dek_slot0(&low_m_entry, b"pw", &[]).err(),
            Some(VaultError::Crypto(CryptoError::InvalidParameter))
        );
    }

    fn test_salt32() -> [u8; SLOT1_SALT_LEN] {
        [0x1A; SLOT1_SALT_LEN]
    }

    fn test_prf_secret() -> [u8; SLOT1_MIN_PRF_LEN] {
        [0x5A; SLOT1_MIN_PRF_LEN]
    }

    fn test_recovery_secret() -> [u8; SLOT2_MIN_SECRET_LEN] {
        [0xA5; SLOT2_MIN_SECRET_LEN]
    }

    const TEST_RECOVERY_CODE: &[u8] = b"ABCD-EFGH-JKLM-NPQR-STUV-WXYZ-1234";

    #[test]
    fn slot1_prf_wrap_and_unwrap_roundtrip() {
        let dek = test_dek();
        let prf = test_prf_secret();
        let salt = test_salt32();
        let nonce = test_nonce();
        let header = test_header();

        // VaultHeader バインドを付与した Slot 1 のラップと復号の一致を確認。
        let entry = wrap_dek_slot1_for_header(&dek, &prf, &salt, &nonce, &header).unwrap();
        assert_eq!(entry.slot_id(), SLOT_ID_PRF);
        assert_eq!(entry.kdf_kind(), KDF_KIND_HKDF_SHA256);
        assert_eq!(entry.wrapped_dek().len(), SLOT1_WRAPPED_DEK_LEN);
        assert!(is_valid_slot1_entry(&entry));

        let unwrapped = unwrap_dek_slot1_for_header(&entry, &prf, &header).unwrap();
        assert_eq!(unwrapped.as_bytes(), dek.as_bytes());
    }

    #[test]
    fn slot1_prf_binary_layout_and_short_secret_rejected() {
        let dek = test_dek();
        let prf = [0x3C; 64];
        let salt = test_salt32();
        let nonce = test_nonce();

        // 32バイトを超える PRF 出力における正常なラップと復号の成立を確認。
        let entry = wrap_dek_slot1(&dek, &prf, &salt, &nonce, b"aad").unwrap();
        let payload = PrfSlotPayload::from_slot_entry(&entry).unwrap();
        assert_eq!(payload.salt, salt);
        assert_eq!(payload.nonce, nonce);
        assert_eq!(payload.to_bytes(), entry.wrapped_dek());

        let unwrapped = unwrap_dek_slot1(&entry, &prf, b"aad").unwrap();
        assert_eq!(unwrapped.as_bytes(), dek.as_bytes());

        // 低エントロピー防止のため 32バイト未満の PRF 入力の拒絶を確認。
        let short_prf = [0x11; SLOT1_MIN_PRF_LEN - 1];
        assert_eq!(
            wrap_dek_slot1(&dek, &short_prf, &salt, &nonce, b"aad"),
            Err(VaultError::Crypto(CryptoError::InvalidKeySize))
        );
        assert_eq!(
            unwrap_dek_slot1(&entry, &short_prf, b"aad").err(),
            Some(VaultError::Crypto(CryptoError::InvalidKeySize))
        );
    }

    #[test]
    fn slot1_prf_wrong_secret_aad_and_tamper_fail() {
        let dek = test_dek();
        let prf = test_prf_secret();
        let header = test_header();
        let entry =
            wrap_dek_slot1_for_header(&dek, &prf, &test_salt32(), &test_nonce(), &header).unwrap();

        // 異なる PRF 出力における AEAD 復号の失敗を確認。
        let mut wrong_prf = prf;
        wrong_prf[0] ^= 0x01;
        assert_eq!(
            unwrap_dek_slot1_for_header(&entry, &wrong_prf, &header).err(),
            Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
        );

        // AAD バインドによる epoch_id 変更 (ロールバック攻撃相当) の検知を確認。
        let mut rolled_back = header;
        rolled_back.epoch_id += 1;
        assert_eq!(
            unwrap_dek_slot1_for_header(&entry, &prf, &rolled_back).err(),
            Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
        );

        // wrapped_dek 全104バイトにおける任意の 1ビット改ざん検知を確認。
        for pos in 0..SLOT1_WRAPPED_DEK_LEN {
            let mut tampered = entry.wrapped_dek().to_vec();
            tampered[pos] ^= 0x01;
            let tampered_entry =
                KekSlotEntry::new(SLOT_ID_PRF, KDF_KIND_HKDF_SHA256, tampered).unwrap();
            assert_eq!(
                unwrap_dek_slot1_for_header(&tampered_entry, &prf, &header).err(),
                Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
            );
        }

        // slot_id や kdf_kind の不一致、および長さ不正ペイロードの拒絶を確認。
        let wrong_id = KekSlotEntry::new(
            SLOT_ID_RECOVERY,
            KDF_KIND_HKDF_SHA256,
            entry.wrapped_dek().to_vec(),
        )
        .unwrap();
        assert!(!is_valid_slot1_entry(&wrong_id));
        assert_eq!(
            unwrap_dek_slot1_for_header(&wrong_id, &prf, &header).err(),
            Some(VaultError::Parse(TlvParseError::InvalidFormat))
        );

        let wrong_kdf =
            KekSlotEntry::new(SLOT_ID_PRF, KDF_KIND_RECOVERY, entry.wrapped_dek().to_vec())
                .unwrap();
        assert!(!is_valid_slot1_entry(&wrong_kdf));
        assert_eq!(
            unwrap_dek_slot1_for_header(&wrong_kdf, &prf, &header).err(),
            Some(VaultError::Parse(TlvParseError::InvalidFormat))
        );
        assert_eq!(
            PrfSlotPayload::from_bytes(&entry.wrapped_dek()[..SLOT1_WRAPPED_DEK_LEN - 1]),
            Err(VaultError::Parse(TlvParseError::InvalidLength))
        );
    }

    #[test]
    fn slot2_recovery_secret_and_code_roundtrip() {
        let dek = test_dek();
        let secret = test_recovery_secret();
        let header = test_header();

        // 生リカバリーシークレットによるラップと復号の成立を確認。
        let raw_entry =
            wrap_dek_slot2_for_header(&dek, &secret, &test_salt32(), &test_nonce(), &header)
                .unwrap();
        assert_eq!(raw_entry.slot_id(), SLOT_ID_RECOVERY);
        assert_eq!(raw_entry.kdf_kind(), KDF_KIND_RECOVERY);
        assert_eq!(raw_entry.wrapped_dek().len(), SLOT2_WRAPPED_DEK_LEN);
        assert!(is_valid_slot2_entry(&raw_entry));
        let unwrapped_raw = unwrap_dek_slot2_for_header(&raw_entry, &secret, &header).unwrap();
        assert_eq!(unwrapped_raw.as_bytes(), dek.as_bytes());

        // 整形済み英数字リカバリーコードにおいて 小文字, ハイフン, 空白 の差異を吸収して復号できることを確認。
        let code_entry = wrap_dek_slot2_code_for_header(
            &dek,
            TEST_RECOVERY_CODE,
            &test_salt32(),
            &test_nonce(),
            &header,
        )
        .unwrap();
        let variant = b"  abcd efgh-jklm npqr stuv wxyz 1234  ";
        let unwrapped_code =
            unwrap_dek_slot2_code_for_header(&code_entry, variant, &header).unwrap();
        assert_eq!(unwrapped_code.as_bytes(), dek.as_bytes());
    }

    #[test]
    fn slot2_normalization_and_validation_rules() {
        let normalized = normalize_recovery_code(b"ab cd-1234-efgh-5678-ijkl-mnop-qr").unwrap();
        assert_eq!(normalized.as_slice(), b"ABCD1234EFGH5678IJKLMNOPQR");

        // 24文字未満の短小コードの拒絶を確認。
        assert_eq!(
            normalize_recovery_code(b"ABCD-EFGH-IJKL-MNOP-QRST-123").err(),
            Some(VaultError::Crypto(CryptoError::InvalidKeySize))
        );

        // 未許可記号を含むコードにおけるパラメータ不正の発生を確認。
        assert_eq!(
            normalize_recovery_code(b"ABCD-EFGH-IJKL-MNOP-QRST-UVW!").err(),
            Some(VaultError::Crypto(CryptoError::InvalidParameter))
        );

        // 境界チェックによる過長入力 DoS の拒絶を確認。
        let oversized = vec![b'A'; MAX_RECOVERY_CODE_INPUT_LEN + 1];
        assert_eq!(
            normalize_recovery_code(&oversized).err(),
            Some(VaultError::Crypto(CryptoError::InvalidSliceLength))
        );

        // 16バイト未満の生シークレット拒絶を確認。
        let dek = test_dek();
        let short_secret = [0x99; SLOT2_MIN_SECRET_LEN - 1];
        assert_eq!(
            wrap_dek_slot2(&dek, &short_secret, &test_salt32(), &test_nonce(), b"aad"),
            Err(VaultError::Crypto(CryptoError::InvalidKeySize))
        );
    }

    #[test]
    fn slot1_and_slot2_domain_separation_prevents_cross_slot_unwrap() {
        let dek = test_dek();
        let shared_secret = [0x77; 32];
        let header = test_header();

        // 同一の ソルト, ノンス, 鍵素材, ヘッダー であっても Slot 1 と Slot 2 が完全に分離されることを確認。
        let slot1 =
            wrap_dek_slot1_for_header(&dek, &shared_secret, &test_salt32(), &test_nonce(), &header)
                .unwrap();
        let slot2 =
            wrap_dek_slot2_for_header(&dek, &shared_secret, &test_salt32(), &test_nonce(), &header)
                .unwrap();
        assert_ne!(slot1.wrapped_dek(), slot2.wrapped_dek());

        // AAD および HKDF-info の分離により、Slot 1 ペイロードの Slot 2 への偽装復号が失敗することを確認。
        let forged_slot2 = KekSlotEntry::new(
            SLOT_ID_RECOVERY,
            KDF_KIND_RECOVERY,
            slot1.wrapped_dek().to_vec(),
        )
        .unwrap();
        assert_eq!(
            unwrap_dek_slot2_for_header(&forged_slot2, &shared_secret, &header).err(),
            Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
        );

        let forged_slot1 = KekSlotEntry::new(
            SLOT_ID_PRF,
            KDF_KIND_HKDF_SHA256,
            slot2.wrapped_dek().to_vec(),
        )
        .unwrap();
        assert_eq!(
            unwrap_dek_slot1_for_header(&forged_slot1, &shared_secret, &header).err(),
            Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
        );
    }

    #[test]
    fn inspect_kek_slots_validates_all_three_slots() {
        let dek = test_dek();
        let header = test_header();
        let slot0 = wrap_dek_slot0_for_header(
            &dek,
            b"password",
            &test_salt(),
            &test_nonce(),
            &test_params(),
            &header,
        )
        .unwrap();
        let slot1 = wrap_dek_slot1_for_header(
            &dek,
            &test_prf_secret(),
            &test_salt32(),
            &test_nonce(),
            &header,
        )
        .unwrap();
        let slot2 = wrap_dek_slot2_for_header(
            &dek,
            &test_recovery_secret(),
            &test_salt32(),
            &test_nonce(),
            &header,
        )
        .unwrap();

        let inspected = inspect_kek_slots(&[slot0.clone(), slot1.clone(), slot2.clone()]);
        assert_eq!(inspected.status_of(SlotKind::Argon2id), SlotStatus::Valid);
        assert_eq!(inspected.status_of(SlotKind::Prf), SlotStatus::Valid);
        assert_eq!(inspected.status_of(SlotKind::Recovery), SlotStatus::Valid);

        // Slot 1 の破損や Slot 2 の重複が存在しても、健全な Slot 0 が影響を受けないことを確認。
        let bad_slot1 = KekSlotEntry::new(SLOT_ID_PRF, KDF_KIND_HKDF_SHA256, vec![0; 10]).unwrap();
        let partial = inspect_kek_slots(&[slot0, bad_slot1, slot2.clone(), slot2]);
        assert_eq!(partial.status_of(SlotKind::Argon2id), SlotStatus::Valid);
        assert_eq!(partial.status_of(SlotKind::Prf), SlotStatus::Invalid);
        assert_eq!(partial.status_of(SlotKind::Recovery), SlotStatus::Invalid);
    }

    #[test]
    fn slot_multiplexing_soundness_any_single_valid_slot_unlocks() {
        let dek = test_dek();
        let header = test_header();
        let header_aad = header.associated_data();
        let password = b"master-password";
        let prf = test_prf_secret();
        let recovery_code = TEST_RECOVERY_CODE;

        let slot0 = wrap_dek_slot0_for_header(
            &dek,
            password,
            &test_salt(),
            &test_nonce(),
            &test_params(),
            &header,
        )
        .unwrap();
        let slot1 =
            wrap_dek_slot1_for_header(&dek, &prf, &[0x21; 32], &[0x31; 24], &header).unwrap();
        let slot2 =
            wrap_dek_slot2_code_for_header(&dek, recovery_code, &[0x22; 32], &[0x32; 24], &header)
                .unwrap();

        // 3スロット構成の Vault において Slot 0, Slot 1, Slot 2 のいずれでも単独解錠できることを確認。
        let vault_all = Vault::new(
            header,
            vec![slot0.clone(), slot1.clone(), slot2.clone()],
            vec![],
        );
        for cred in [
            SlotCredential::password(password),
            SlotCredential::prf(&prf),
            SlotCredential::recovery_code(recovery_code),
        ] {
            let mut engine = VaultEngine::from_slot_entries(&vault_all.slots);
            let used = engine.unlock_vault_with_any(&vault_all, &[cred]).unwrap();
            assert_eq!(used, cred.slot_kind());
            assert_eq!(engine.state(), VaultState::Unlocked);
            assert_eq!(engine.dek().unwrap().as_bytes(), dek.as_bytes());
        }

        // 先行スロットが 未設定, 破損, 誤認証 のいずれであっても後続の有効スロットで解錠でき、
        // 全スロット失敗時は安全に Locked 状態へ復帰することを確認。
        let corrupted_slot0 =
            KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, vec![0xFF; 16]).unwrap();
        let mut mixed_slots = vec![corrupted_slot0, slot2.clone()];
        let vault_mixed = Vault::new(header, mixed_slots.clone(), vec![]);
        let mut engine = VaultEngine::from_slot_entries(&vault_mixed.slots);
        assert_eq!(
            engine.slots().status_of(SlotKind::Argon2id),
            SlotStatus::Invalid
        );
        assert_eq!(engine.slots().status_of(SlotKind::Prf), SlotStatus::Unset);
        assert_eq!(
            engine.slots().status_of(SlotKind::Recovery),
            SlotStatus::Valid
        );

        let used = engine
            .unlock_vault_with_any(
                &vault_mixed,
                &[
                    SlotCredential::password(password),
                    SlotCredential::prf(&prf),
                    SlotCredential::recovery_code(b"WRONG-CODE-XXXX-YYYY-ZZZZ-1234"),
                    SlotCredential::recovery_code(recovery_code),
                ],
            )
            .unwrap();
        assert_eq!(used, SlotKind::Recovery);
        assert_eq!(engine.dek().unwrap().as_bytes(), dek.as_bytes());

        // 解錠状態からの追加スロット生成 (Slot 1, Slot 2) および施錠後の再解錠を確認。
        let minted_slot1 = engine
            .wrap_slot1(&[0xEE; 32], &[0x44; 32], &[0x55; 24], &header_aad)
            .unwrap();
        let minted_slot2 = engine
            .wrap_slot2(&[0xDD; 32], &[0x46; 32], &[0x57; 24], &header_aad)
            .unwrap();
        let minted_slot2_code = engine
            .wrap_slot2_code(recovery_code, &[0x48; 32], &[0x59; 24], &header_aad)
            .unwrap();
        engine.lock().unwrap();

        mixed_slots.push(minted_slot1);
        let vault_prf_added = Vault::new(header, mixed_slots, vec![]);
        let mut engine2 = VaultEngine::from_slot_entries(&vault_prf_added.slots);
        assert!(
            engine2
                .unlock_vault_with_prf(&vault_prf_added, &[0xEE; 32])
                .is_ok()
        );

        let vault_raw_rec = Vault::new(header, vec![minted_slot2], vec![]);
        let mut engine3 = VaultEngine::from_slot_entries(&vault_raw_rec.slots);
        assert!(
            engine3
                .unlock_vault_with_recovery(&vault_raw_rec, &[0xDD; 32])
                .is_ok()
        );

        let vault_code_rec = Vault::new(header, vec![minted_slot2_code], vec![]);
        let mut engine4 = VaultEngine::from_slot_entries(&vault_code_rec.slots);
        assert!(
            engine4
                .unlock_vault_with_recovery_code(&vault_code_rec, recovery_code)
                .is_ok()
        );

        // 全候補失敗時のエラー返却、およびエンジンが安全に Locked を維持することを確認。
        engine4.lock().unwrap();
        assert!(
            engine4
                .unlock_vault_with_any(
                    &vault_code_rec,
                    &[
                        SlotCredential::prf(&prf),
                        SlotCredential::recovery(b"short")
                    ],
                )
                .is_err()
        );
        assert_eq!(engine4.state(), VaultState::Locked);
        assert!(engine4.dek().is_err());

        // Slot 1 のみ設定された状態からの単一スロット解錠を確認。
        let vault_slot1_only = Vault::new(header, vec![slot1], vec![]);
        let mut engine5 = VaultEngine::from_slot_entries(&vault_slot1_only.slots);
        assert!(
            engine5
                .unlock_vault_with_prf(&vault_slot1_only, &prf)
                .is_ok()
        );
        assert_eq!(engine5.dek().unwrap().as_bytes(), dek.as_bytes());
    }

    #[test]
    fn slot_credential_debug_redacts_secrets() {
        let dbg_pwd = format!("{:?}", SlotCredential::password(b"top-secret"));
        let dbg_prf = format!("{:?}", SlotCredential::prf(b"prf-secret"));
        let dbg_rec = format!("{:?}", SlotCredential::recovery(b"rec-secret"));
        let dbg_code = format!("{:?}", SlotCredential::recovery_code(b"code-secret"));
        assert!(!dbg_pwd.contains("top-secret"));
        assert!(!dbg_prf.contains("prf-secret"));
        assert!(!dbg_rec.contains("rec-secret"));
        assert!(!dbg_code.contains("code-secret"));
    }

    #[test]
    fn test_unlock_vault_with_any_runs_dummy_ops_for_remaining_slots() {
        let dek = test_dek();
        let header = test_header();
        let password = b"master-password";
        let prf = test_prf_secret();
        let recovery_code = TEST_RECOVERY_CODE;

        let slot0 = wrap_dek_slot0_for_header(
            &dek,
            password,
            &test_salt(),
            &test_nonce(),
            &test_params(),
            &header,
        )
        .unwrap();
        let slot1 =
            wrap_dek_slot1_for_header(&dek, &prf, &[0x21; 32], &[0x31; 24], &header).unwrap();
        let slot2 =
            wrap_dek_slot2_code_for_header(&dek, recovery_code, &[0x22; 32], &[0x32; 24], &header)
                .unwrap();
        let vault = Vault::new(header, vec![slot0, slot1, slot2], vec![]);

        // 先頭 Slot 0 が成功しても、後続の Slot 1 / Slot 2 に対してダミー暗号演算が実行される。
        let mut engine =
            VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(test_params());
        let (res, trace) = engine.unlock_vault_with_any_traced(
            &vault,
            &[
                SlotCredential::password(password),
                SlotCredential::prf(&[0x99; 32]),
                SlotCredential::recovery_code(b"WRONG-CODE-XXXX-YYYY-ZZZZ-1234"),
            ],
            false,
        );
        assert_eq!(res, Ok(SlotKind::Argon2id));
        assert_eq!(trace.real_argon2id_ops, 1);
        assert_eq!(trace.dummy_argon2id_ops, 0);
        assert_eq!(trace.real_hkdf_ops, 0);
        assert_eq!(trace.dummy_hkdf_ops, 2);
        assert_eq!(trace.real_aead_ops, 1);
        assert_eq!(trace.dummy_aead_ops, 2);
        assert_eq!(trace.total_kdf_ops(), 3);
        assert_eq!(trace.total_aead_ops(), 3);
        assert_eq!(engine.dek().unwrap().as_bytes(), dek.as_bytes());

        // 先頭 Slot 1 (PRF) が成功しても、残余の Slot 0 (Argon2id) と Slot 2 にダミー演算が実行される。
        let mut engine_prf =
            VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(test_params());
        let (res, trace) = engine_prf.unlock_vault_with_any_traced(
            &vault,
            &[
                SlotCredential::prf(&prf),
                SlotCredential::password(b"wrong-pw"),
                SlotCredential::recovery_code(b"WRONG-CODE-XXXX-YYYY-ZZZZ-1234"),
            ],
            false,
        );
        assert_eq!(res, Ok(SlotKind::Prf));
        assert_eq!(trace.real_argon2id_ops, 0);
        assert_eq!(trace.dummy_argon2id_ops, 1);
        assert_eq!(trace.real_hkdf_ops, 1);
        assert_eq!(trace.dummy_hkdf_ops, 1);
        assert_eq!(trace.real_aead_ops, 1);
        assert_eq!(trace.dummy_aead_ops, 2);
        assert_eq!(engine_prf.dek().unwrap().as_bytes(), dek.as_bytes());

        // 全候補が有効な場合でも最初の成功スロットが採用され、残余は実復号ではなくダミー演算のみ実行する。
        let mut engine_all_valid =
            VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(test_params());
        let (res, trace) = engine_all_valid.unlock_vault_with_any_traced(
            &vault,
            &[
                SlotCredential::recovery_code(recovery_code),
                SlotCredential::password(password),
                SlotCredential::prf(&prf),
            ],
            false,
        );
        assert_eq!(res, Ok(SlotKind::Recovery));
        assert_eq!(trace.real_argon2id_ops, 0);
        assert_eq!(trace.dummy_argon2id_ops, 1);
        assert_eq!(trace.real_hkdf_ops, 1);
        assert_eq!(trace.dummy_hkdf_ops, 1);
        assert_eq!(trace.real_aead_ops, 1);
        assert_eq!(trace.dummy_aead_ops, 2);
        assert_eq!(engine_all_valid.dek().unwrap().as_bytes(), dek.as_bytes());
    }

    #[test]
    fn test_missing_corrupted_duplicate_and_invalid_inputs_run_dummy_ops() {
        let dek = test_dek();
        let header = test_header();
        let header_aad = header.associated_data();
        let prf = test_prf_secret();

        // 空の Vault に対する各スロット解錠ではダミー暗号演算を実行し、
        // 内部詳細エラー(SlotNotFound)を漏らさず単一の AuthenticationFailed を返す。
        let empty_vault = Vault::new(header, vec![], vec![]);
        let mut empty_engine = VaultEngine::from_slot_entries(&empty_vault.slots)
            .with_dummy_argon2_params(test_params());

        let mut trace_pw = SlotEvalTrace::default();
        assert_eq!(
            empty_engine.unlock_vault_with_credential_traced(
                &empty_vault,
                SlotCredential::password(b"pw"),
                &mut trace_pw,
            ),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(trace_pw.dummy_argon2id_ops, 1);
        assert_eq!(trace_pw.dummy_aead_ops, 1);

        let mut trace_prf = SlotEvalTrace::default();
        assert_eq!(
            empty_engine.unlock_vault_with_credential_traced(
                &empty_vault,
                SlotCredential::prf(&prf),
                &mut trace_prf,
            ),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(trace_prf.dummy_hkdf_ops, 1);
        assert_eq!(trace_prf.dummy_aead_ops, 1);

        let mut trace_rec = SlotEvalTrace::default();
        assert_eq!(
            empty_engine.unlock_vault_with_credential_traced(
                &empty_vault,
                SlotCredential::recovery_code(b"invalid!"),
                &mut trace_rec,
            ),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(trace_rec.dummy_hkdf_ops, 1);
        assert_eq!(trace_rec.dummy_aead_ops, 1);
        assert_eq!(empty_engine.state(), VaultState::Locked);

        // 重複スロットおよび短小入力, 破損フォーマットでもダミー演算がちょうど 1 回実行され、
        // 外部境界では単一の AuthenticationFailed へ一様マスキングされる。
        let slot1 =
            wrap_dek_slot1_for_header(&dek, &prf, &test_salt32(), &test_nonce(), &header).unwrap();
        let dup_vault = Vault::new(header, vec![slot1.clone(), slot1.clone()], vec![]);
        let mut dup_engine = VaultEngine::from_slot_entries(&dup_vault.slots)
            .with_dummy_argon2_params(test_params());
        let mut trace_dup = SlotEvalTrace::default();
        assert_eq!(
            dup_engine.unlock_vault_with_credential_traced(
                &dup_vault,
                SlotCredential::prf(&prf),
                &mut trace_dup,
            ),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(trace_dup.dummy_hkdf_ops, 1);
        assert_eq!(trace_dup.dummy_aead_ops, 1);

        // 単一スロットメソッドの Unset/Invalid/入力不正に対するダミー演算保証を確認。
        let mut unset_engine = VaultEngine::locked().with_dummy_argon2_params(test_params());
        let valid_slot0 = wrap_dek_slot0_for_header(
            &dek,
            b"pw",
            &test_salt(),
            &test_nonce(),
            &test_params(),
            &header,
        )
        .unwrap();
        let mut trace_s0 = SlotEvalTrace::default();
        assert_eq!(
            unset_engine.unlock_with_slot0_with_secret_traced(
                &valid_slot0,
                b"pw",
                &[],
                &header_aad,
                &mut trace_s0,
            ),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(trace_s0.dummy_argon2id_ops, 1);
        assert_eq!(trace_s0.dummy_aead_ops, 1);

        let mut trace_s1 = SlotEvalTrace::default();
        assert_eq!(
            unset_engine.unlock_with_slot1_traced(&slot1, &prf, &header_aad, &mut trace_s1),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(trace_s1.dummy_hkdf_ops, 1);
        assert_eq!(trace_s1.dummy_aead_ops, 1);

        let slot2_code = wrap_dek_slot2_code_for_header(
            &dek,
            TEST_RECOVERY_CODE,
            &test_salt32(),
            &test_nonce(),
            &header,
        )
        .unwrap();
        let mut valid_s2_engine =
            VaultEngine::from_slot_entries(core::slice::from_ref(&slot2_code));
        let mut trace_bad_code = SlotEvalTrace::default();
        assert_eq!(
            valid_s2_engine.unlock_with_slot2_code_traced(
                &slot2_code,
                b"SHORT!",
                &header_aad,
                &mut trace_bad_code,
            ),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(trace_bad_code.dummy_hkdf_ops, 1);
        assert_eq!(trace_bad_code.dummy_aead_ops, 1);
    }

    #[test]
    fn test_dummy_slot_eval_pipeline_execution() {
        let aad = b"test_vault_aad_payload";
        let summary = run_dummy_slot_eval_for_inspection(aad);
        assert_eq!(summary.dummy_argon2id_ops, 1);
        assert_eq!(summary.dummy_hkdf_ops, 2);
        assert_eq!(summary.dummy_aead_ops, 3);

        // 空AADおよび過大AADに対しても安全にフォールバックダミー演算が完結することを確認。
        let empty_summary = run_dummy_slot_eval_for_inspection(&[]);
        assert_eq!(empty_summary.dummy_argon2id_ops, 1);
        assert_eq!(empty_summary.dummy_hkdf_ops, 2);
        assert_eq!(empty_summary.dummy_aead_ops, 3);

        let huge_aad = [0x5Au8; 2048];
        let huge_summary = run_dummy_slot_eval_for_inspection(&huge_aad);
        assert_eq!(huge_summary.dummy_argon2id_ops, 1);
        assert_eq!(huge_summary.dummy_hkdf_ops, 2);
        assert_eq!(huge_summary.dummy_aead_ops, 3);
    }

    #[test]
    fn test_external_unlock_apis_uniformly_mask_internal_errors() {
        let dek = test_dek();
        let header = test_header();
        let header_aad = header.associated_data();
        let password = b"correct-password";
        let pepper = b"app-pepper";
        let prf = test_prf_secret();
        let recovery = test_recovery_secret();
        let recovery_code = TEST_RECOVERY_CODE;

        let slot0 = wrap_dek_slot0_with_secret(
            &dek,
            password,
            &test_salt(),
            &test_nonce(),
            &test_params(),
            pepper,
            &header_aad,
        )
        .unwrap();
        let slot1 =
            wrap_dek_slot1_for_header(&dek, &prf, &test_salt32(), &test_nonce(), &header).unwrap();
        let slot2_raw =
            wrap_dek_slot2_for_header(&dek, &recovery, &test_salt32(), &test_nonce(), &header)
                .unwrap();
        let slot2_code = wrap_dek_slot2_code_for_header(
            &dek,
            recovery_code,
            &test_salt32(),
            &test_nonce(),
            &header,
        )
        .unwrap();

        // 低レベルプリミティブ層は詳細エラーを温存していることを確認する。
        assert_eq!(
            find_slot_entry(&[], SLOT_ID_ARGON2ID),
            Err(VaultError::SlotNotFound)
        );
        assert_eq!(
            unwrap_dek_slot0(&slot0, b"wrong", &header_aad).err(),
            Some(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
        );
        assert_eq!(
            unwrap_dek_slot1(&slot1, b"short", &header_aad).err(),
            Some(VaultError::Crypto(CryptoError::InvalidKeySize))
        );
        assert_eq!(
            normalize_recovery_code(b"INVALID!").err(),
            Some(VaultError::Crypto(CryptoError::InvalidParameter))
        );

        // 単一スロット公開API境界: 不正フォーマット, 不正長さ, 不正パラメータ, MAC不一致, 入力不正が
        // すべて単一の AuthenticationFailed へ一様マスキングされる。
        let valid_vault = Vault::new(
            header,
            vec![slot0.clone(), slot1.clone(), slot2_raw.clone()],
            vec![],
        );
        let mut engine = VaultEngine::from_slot_entries(&valid_vault.slots)
            .with_dummy_argon2_params(test_params());

        let wrong_id_slot0 =
            KekSlotEntry::new(SLOT_ID_PRF, KDF_KIND_ARGON2ID, slot0.wrapped_dek().to_vec())
                .unwrap();
        let bad_len_slot0 =
            KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, vec![0x11; 10]).unwrap();
        let mut bad_param_bytes = slot0.wrapped_dek().to_vec();
        bad_param_bytes[0..4].copy_from_slice(&(MAX_SLOT0_M_COST + 1).to_be_bytes());
        let bad_param_slot0 =
            KekSlotEntry::new(SLOT_ID_ARGON2ID, KDF_KIND_ARGON2ID, bad_param_bytes).unwrap();

        let slot0_failures = [
            engine.unlock_with_slot0(&slot0, password, &header_aad),
            engine.unlock_with_slot0_with_secret(&slot0, password, b"wrong-pepper", &header_aad),
            engine.unlock_with_slot0_with_secret(&slot0, b"wrong-pw", pepper, &header_aad),
            engine.unlock_with_slot0_with_secret(&slot0, password, pepper, b"tampered-aad"),
            engine.unlock_with_slot0(&wrong_id_slot0, password, &header_aad),
            engine.unlock_with_slot0(&bad_len_slot0, password, &header_aad),
            engine.unlock_with_slot0(&bad_param_slot0, password, &header_aad),
        ];
        for res in slot0_failures {
            assert_eq!(res, Err(VaultError::AuthenticationFailed));
            assert_eq!(engine.state(), VaultState::Locked);
            assert!(engine.is_safe_state());
            assert!(engine.observe_dek().is_none());
        }

        let bad_len_slot1 =
            KekSlotEntry::new(SLOT_ID_PRF, KDF_KIND_HKDF_SHA256, vec![0x22; 16]).unwrap();
        let wrong_id_slot1 = KekSlotEntry::new(
            SLOT_ID_RECOVERY,
            KDF_KIND_HKDF_SHA256,
            slot1.wrapped_dek().to_vec(),
        )
        .unwrap();
        for res in [
            engine.unlock_with_slot1(&slot1, &[0x99; SLOT1_MIN_PRF_LEN], &header_aad),
            engine.unlock_with_slot1(&slot1, b"too-short", &header_aad),
            engine.unlock_with_slot1(&bad_len_slot1, &prf, &header_aad),
            engine.unlock_with_slot1(&wrong_id_slot1, &prf, &header_aad),
            engine.unlock_with_slot1(&slot1, &prf, b"wrong-aad"),
        ] {
            assert_eq!(res, Err(VaultError::AuthenticationFailed));
            assert_eq!(engine.state(), VaultState::Locked);
        }

        let bad_len_slot2 =
            KekSlotEntry::new(SLOT_ID_RECOVERY, KDF_KIND_RECOVERY, vec![0x33; 16]).unwrap();
        for res in [
            engine.unlock_with_slot2(&slot2_raw, &[0x00; SLOT2_MIN_SECRET_LEN], &header_aad),
            engine.unlock_with_slot2(&slot2_raw, b"short", &header_aad),
            engine.unlock_with_slot2(&bad_len_slot2, &recovery, &header_aad),
            engine.unlock_with_slot2_code(&slot2_code, b"SHORT", &header_aad),
            engine.unlock_with_slot2_code(
                &slot2_code,
                b"BAD!-CODE-1234-5678-9012-3456",
                &header_aad,
            ),
            engine.unlock_with_slot2_code(
                &slot2_code,
                b"AAAA-BBBB-CCCC-DDDD-EEEE-FFFF-GGGG",
                &header_aad,
            ),
        ] {
            assert_eq!(res, Err(VaultError::AuthenticationFailed));
            assert_eq!(engine.state(), VaultState::Locked);
        }

        // Vault 全体の解錠公開API境界:
        // スロット不在, 重複, 破損, 誤認証, 入力不足のすべてが同一の AuthenticationFailed に収束する。
        let empty_vault = Vault::new(header, vec![], vec![]);
        let dup_vault = Vault::new(
            header,
            vec![
                slot0.clone(),
                slot0.clone(),
                slot1.clone(),
                slot1.clone(),
                slot2_raw.clone(),
                slot2_raw.clone(),
            ],
            vec![],
        );
        let corrupt_vault = Vault::new(
            header,
            vec![bad_len_slot0, bad_len_slot1, bad_len_slot2],
            vec![],
        );
        let rollback_header = VaultHeader {
            epoch_id: header.epoch_id - 1,
            ..header
        };
        let rollback_vault = Vault::new(rollback_header, vec![slot0, slot1, slot2_code], vec![]);

        for target_vault in [
            &empty_vault,
            &dup_vault,
            &corrupt_vault,
            &valid_vault,
            &rollback_vault,
        ] {
            let mut v_engine = VaultEngine::from_slot_entries(&target_vault.slots)
                .with_dummy_argon2_params(test_params());

            let wrong_creds = [
                SlotCredential::password(b"wrong-password"),
                SlotCredential::prf(b"short-prf"),
                SlotCredential::recovery(b"short-rec"),
                SlotCredential::recovery_code(b"INVALID!"),
            ];
            for res in [
                v_engine.unlock_vault_with_password(target_vault, b"wrong-password"),
                v_engine.unlock_vault_with_prf(target_vault, b"short-prf"),
                v_engine.unlock_vault_with_recovery(target_vault, b"short-rec"),
                v_engine.unlock_vault_with_recovery_code(target_vault, b"INVALID!"),
                v_engine.unlock_vault_with_credential(
                    target_vault,
                    SlotCredential::password_with_secret(password, b"wrong-pepper"),
                ),
                v_engine
                    .unlock_vault_with_any(target_vault, &wrong_creds)
                    .map(|_| ()),
                v_engine
                    .unlock_vault_with_all_slots(target_vault, &wrong_creds)
                    .map(|_| ()),
                v_engine
                    .unlock_vault_with_any(target_vault, &[])
                    .map(|_| ()),
                v_engine
                    .unlock_vault_with_all_slots(target_vault, &[])
                    .map(|_| ()),
            ] {
                assert_eq!(res, Err(VaultError::AuthenticationFailed));
                assert_eq!(v_engine.state(), VaultState::Locked);
                assert!(v_engine.is_safe_state());
                assert!(v_engine.observe_dek().is_none());
            }
        }

        // FSM の公開状態契約違反 (Unlocked / Zeroized) は InvalidState として維持される。
        engine
            .unlock_vault_with_recovery(&valid_vault, &recovery)
            .unwrap();
        assert_eq!(engine.state(), VaultState::Unlocked);
        assert_eq!(
            engine.unlock_vault_with_password(&empty_vault, b"pw"),
            Err(VaultError::InvalidState)
        );
        assert_eq!(
            engine.unlock_vault_with_any(&empty_vault, &[SlotCredential::prf(&prf)]),
            Err(VaultError::InvalidState)
        );
        engine.zeroize_key().unwrap();
        assert_eq!(
            engine.unlock_vault_with_all_slots(&valid_vault, &[SlotCredential::prf(&prf)]),
            Err(VaultError::InvalidState)
        );
    }

    #[test]
    fn test_unlock_vault_with_all_slots_covers_all_three_slot_kinds() {
        let dek = test_dek();
        let header = test_header();
        let prf = test_prf_secret();
        let slot0 = wrap_dek_slot0_for_header(
            &dek,
            b"pw",
            &test_salt(),
            &test_nonce(),
            &test_params(),
            &header,
        )
        .unwrap();
        let slot1 =
            wrap_dek_slot1_for_header(&dek, &prf, &test_salt32(), &test_nonce(), &header).unwrap();
        let vault = Vault::new(header, vec![slot0, slot1], vec![]);

        // PRF のみ提示した場合でも Slot 0 (Argon2id) と Slot 2 (Recovery) のダミー演算が補完される。
        let mut engine =
            VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(test_params());
        let (res, trace) =
            engine.unlock_vault_with_any_traced(&vault, &[SlotCredential::prf(&prf)], true);
        assert_eq!(res, Ok(SlotKind::Prf));
        assert_eq!(trace.argon2id_ops(), 1);
        assert_eq!(trace.hkdf_ops(), 2);
        assert_eq!(trace.total_kdf_ops(), 3);
        assert_eq!(trace.total_aead_ops(), 3);

        // 公開ラッパー unlock_vault_with_all_slots でも空リスト含め安全に動作する。
        let mut engine_empty =
            VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(test_params());
        assert_eq!(
            engine_empty.unlock_vault_with_all_slots(&vault, &[]),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(engine_empty.state(), VaultState::Locked);
        assert!(engine_empty.is_safe_state());

        // 同一 SlotKind の複数候補を渡した場合でもすべての候補が評価され、
        // かつ 1 件目が誤り・2 件目が正当な資格情報の場合に正常に解錠できることを確認する。
        let wrong_pw = b"wrong-password";
        let correct_pw = b"pw";
        let mut engine_multi =
            VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(test_params());
        let (multi_res, multi_trace) = engine_multi.unlock_vault_with_any_traced(
            &vault,
            &[
                SlotCredential::password(wrong_pw),
                SlotCredential::password(correct_pw),
            ],
            true,
        );
        assert_eq!(multi_res, Ok(SlotKind::Argon2id));
        assert_eq!(multi_trace.argon2id_ops(), 2);
        assert_eq!(multi_trace.hkdf_ops(), 2); // 未提示の PRF, Recovery 各1回
        assert_eq!(multi_trace.total_kdf_ops(), 4);
        assert_eq!(multi_trace.total_aead_ops(), 4);
        assert_eq!(engine_multi.state(), VaultState::Unlocked);

        // 公開ラッパー unlock_vault_with_all_slots でも同様に解錠できることを確認する。
        let mut engine_multi_pub =
            VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(test_params());
        let pub_res = engine_multi_pub.unlock_vault_with_all_slots(
            &vault,
            &[
                SlotCredential::password(wrong_pw),
                SlotCredential::password(correct_pw),
            ],
        );
        assert_eq!(pub_res, Ok(SlotKind::Argon2id));
        assert_eq!(engine_multi_pub.state(), VaultState::Unlocked);

        // 重複 SlotKind を渡した場合でも全候補が評価され、未提示スロット種別のダミー演算も補完される。
        let wrong_pw1 = b"wrong-pw-1";
        let wrong_pw2 = b"wrong-pw-2";
        let wrong_prf = [0x55u8; SLOT1_MIN_PRF_LEN];
        let wrong_rec = [0x66u8; SLOT2_MIN_SECRET_LEN];
        let mut engine_dup =
            VaultEngine::from_slot_entries(&vault.slots).with_dummy_argon2_params(test_params());
        let (dup_res, dup_trace) = engine_dup.unlock_vault_with_any_traced(
            &vault,
            &[
                SlotCredential::password(wrong_pw1),
                SlotCredential::password(wrong_pw2),
                SlotCredential::prf(&wrong_prf),
                SlotCredential::recovery(&wrong_rec),
                SlotCredential::recovery_code(b"WR0N-GC0D-E000-0000-0000-0000-0000"),
            ],
            true,
        );
        assert_eq!(dup_res, Err(VaultError::AuthenticationFailed));
        assert_eq!(dup_trace.argon2id_ops(), 2);
        assert_eq!(dup_trace.hkdf_ops(), 3);
        assert_eq!(dup_trace.total_kdf_ops(), 5);
        assert_eq!(dup_trace.total_aead_ops(), 5);
        assert_eq!(engine_dup.state(), VaultState::Locked);
        assert!(engine_dup.is_safe_state());
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_timing_smoothing_prevents_early_return_short_circuit() {
        // Argon2id 1 回あたりの実行時間がミリ秒単位になるパラメータを設定する。
        let heavy_params = Argon2Params::custom(2048, 4, 1, Some(DEK_LEN)).unwrap();
        let dek = test_dek();
        let header = test_header();
        let password = b"heavy-slot0-password";
        let prf = test_prf_secret();

        let slot0 = wrap_dek_slot0_for_header(
            &dek,
            password,
            &test_salt(),
            &test_nonce(),
            &heavy_params,
            &header,
        )
        .unwrap();
        let slot1 =
            wrap_dek_slot1_for_header(&dek, &prf, &test_salt32(), &test_nonce(), &header).unwrap();
        let vault = Vault::new(header, vec![slot0.clone(), slot1], vec![]);

        // 並列テスト実行時のOSスケジューリング揺らぎを排除するため、複数回計測の最小値で比較する。
        let mut baseline_argon2_ns = u128::MAX;
        for _ in 0..3 {
            let start_base = std::time::Instant::now();
            let _ = unwrap_dek_slot0_for_header(&slot0, password, &header).unwrap();
            baseline_argon2_ns = baseline_argon2_ns.min(start_base.elapsed().as_nanos());
        }

        // 先頭 Slot 1 (PRF) が即座に成功する構成でも、後続 Slot 0 に対するダミー Argon2id が走る。
        let mut prf_first_ns = u128::MAX;
        for _ in 0..3 {
            let mut engine = VaultEngine::from_slot_entries(&vault.slots);
            let start_prf_first = std::time::Instant::now();
            let used = engine
                .unlock_vault_with_any(
                    &vault,
                    &[
                        SlotCredential::prf(&prf),
                        SlotCredential::password(b"wrong-password"),
                    ],
                )
                .unwrap();
            let elapsed = start_prf_first.elapsed().as_nanos();
            prf_first_ns = prf_first_ns.min(elapsed);
            assert_eq!(used, SlotKind::Prf);
            assert_eq!(engine.dek().unwrap().as_bytes(), dek.as_bytes());
        }

        // 演算トレースでもダミー Argon2id が1回実行されていることを決定論的に確認する。
        let mut traced_engine = VaultEngine::from_slot_entries(&vault.slots);
        let (traced_res, trace) = traced_engine.unlock_vault_with_any_traced(
            &vault,
            &[
                SlotCredential::prf(&prf),
                SlotCredential::password(b"wrong-password"),
            ],
            false,
        );
        assert_eq!(traced_res, Ok(SlotKind::Prf));
        assert_eq!(trace.argon2id_ops(), 1);
        assert_eq!(trace.hkdf_ops(), 1);

        assert!(
            prf_first_ns * 2 >= baseline_argon2_ns,
            "先行PRF成功時でも残余Slot 0のダミーArgon2id演算が実行される必要がある (prf_first={prf_first_ns}ns, baseline={baseline_argon2_ns}ns)。"
        );
    }

    #[test]
    fn test_unlock_with_entry_all_credentials_and_error_handling() {
        let dek = test_dek();
        let header = test_header();
        let header_aad = header.associated_data();
        let params = test_params();
        let salt = test_salt();
        let salt32 = test_salt32();
        let nonce = test_nonce();

        let password = b"master-password";
        let pepper = b"pepper-secret";
        let prf = test_prf_secret();
        let recovery = test_recovery_secret();

        let slot0 =
            wrap_dek_slot0_with_secret(&dek, password, &salt, &nonce, &params, pepper, &header_aad)
                .expect("Slot 0 エントリの生成に成功。");
        let slot1 = wrap_dek_slot1(&dek, &prf, &salt32, &nonce, &header_aad)
            .expect("Slot 1 エントリの生成に成功。");
        let slot2_raw = wrap_dek_slot2(&dek, &recovery, &salt32, &nonce, &header_aad)
            .expect("Slot 2 生エントリの生成に成功。");
        let slot2_code =
            wrap_dek_slot2_code(&dek, TEST_RECOVERY_CODE, &salt32, &nonce, &header_aad)
                .expect("Slot 2 コードエントリの生成に成功。");

        // 1. Slot 0: ペッパー付き資格情報での解錠成功。
        let mut engine0 = VaultEngine::from_slot_entries(core::slice::from_ref(&slot0))
            .with_dummy_argon2_params(test_params());
        assert_eq!(
            engine0.unlock_with_entry(
                &slot0,
                SlotCredential::password_with_secret(password, pepper),
                &header_aad
            ),
            Ok(())
        );
        assert_eq!(engine0.state(), VaultState::Unlocked);
        assert_eq!(engine0.dek().unwrap().as_bytes(), dek.as_bytes());

        // 2. 解錠済み状態での二重解錠試行は InvalidState となる。
        assert_eq!(
            engine0.unlock_with_entry(
                &slot0,
                SlotCredential::password_with_secret(password, pepper),
                &header_aad
            ),
            Err(VaultError::InvalidState)
        );

        // 3. Slot 0: 不正パスワード時は AuthenticationFailed でマスキングされ Locked を維持する。
        let mut engine0_fail = VaultEngine::from_slot_entries(core::slice::from_ref(&slot0))
            .with_dummy_argon2_params(test_params());
        assert_eq!(
            engine0_fail.unlock_with_entry(
                &slot0,
                SlotCredential::password_with_secret(b"wrong-password", pepper),
                &header_aad
            ),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(engine0_fail.state(), VaultState::Locked);

        // 4. Slot 1: PRF 資格情報での解錠成功。
        let mut engine1 = VaultEngine::from_slot_entries(core::slice::from_ref(&slot1))
            .with_dummy_argon2_params(test_params());
        assert_eq!(
            engine1.unlock_with_entry(&slot1, SlotCredential::prf(&prf), &header_aad),
            Ok(())
        );
        assert_eq!(engine1.state(), VaultState::Unlocked);

        // 5. Slot 2: 生リカバリーシークレットでの解錠成功。
        let mut engine2_raw = VaultEngine::from_slot_entries(core::slice::from_ref(&slot2_raw))
            .with_dummy_argon2_params(test_params());
        assert_eq!(
            engine2_raw.unlock_with_entry(
                &slot2_raw,
                SlotCredential::recovery(&recovery),
                &header_aad
            ),
            Ok(())
        );
        assert_eq!(engine2_raw.state(), VaultState::Unlocked);

        // 6. Slot 2: 整形済みリカバリーコードでの解錠成功。
        let mut engine2_code = VaultEngine::from_slot_entries(core::slice::from_ref(&slot2_code))
            .with_dummy_argon2_params(test_params());
        assert_eq!(
            engine2_code.unlock_with_entry(
                &slot2_code,
                SlotCredential::recovery_code(TEST_RECOVERY_CODE),
                &header_aad
            ),
            Ok(())
        );
        assert_eq!(engine2_code.state(), VaultState::Unlocked);

        // 7. エントリ種別と資格情報種別の不一致(Slot 0 エントリに PRF 資格情報)
        let mut engine_mismatch = VaultEngine::from_slot_entries(core::slice::from_ref(&slot0))
            .with_dummy_argon2_params(test_params());
        assert_eq!(
            engine_mismatch.unlock_with_entry(&slot0, SlotCredential::prf(&prf), &header_aad),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(engine_mismatch.state(), VaultState::Locked);
    }

    #[test]
    fn test_invalid_slot0_uses_fallback_params_for_dummy_eval() {
        let dek = test_dek();
        let minimal_params = Argon2Params::custom(64, 1, 1, Some(DEK_LEN)).unwrap();
        let entry = wrap_dek_slot0(
            &dek,
            b"pw",
            &test_salt(),
            &test_nonce(),
            &minimal_params,
            b"aad",
        )
        .unwrap();

        let fallback_params = test_params();
        let mut trace = SlotEvalTrace::default();

        // is_slot_valid == false のとき、エントリの minimal_params ではなく fallback_params でダミー演算が実行される。
        let res = eval_slot0_or_dummy(
            Some(&entry),
            false,
            b"pw",
            &[],
            b"aad",
            &fallback_params,
            &mut trace,
        );

        assert_eq!(res.err(), Some(VaultError::AuthenticationFailed));
        assert_eq!(trace.dummy_argon2id_ops, 1);
        assert_eq!(trace.real_argon2id_ops, 0);

        // 重複スロットにより Invalid となったエンジンに対する解錠試行でも一様失敗の確認に成功。
        let dup_vault = Vault::new(test_header(), vec![entry.clone(), entry.clone()], vec![]);
        let mut engine = VaultEngine::from_slot_entries(&dup_vault.slots)
            .with_dummy_argon2_params(fallback_params);
        assert_eq!(
            engine.unlock_vault_with_password(&dup_vault, b"pw"),
            Err(VaultError::AuthenticationFailed)
        );
        assert_eq!(
            engine.unlock_with_entry(&entry, SlotCredential::password(b"pw"), b"aad"),
            Err(VaultError::AuthenticationFailed)
        );
    }

    #[test]
    fn test_vault_engine_from_slot_entries_inherits_slot0_argon2_params() {
        let dek = test_dek();
        let custom_params = Argon2Params::fast_test().with_m_cost(128);
        let header = test_header();
        let entry = wrap_dek_slot0(
            &dek,
            b"test_password",
            &[1u8; SLOT0_SALT_LEN],
            &[2u8; SLOT0_NONCE_LEN],
            &custom_params,
            &header.associated_data(),
        )
        .expect("Slot 0 ラップに成功。");

        // Slot 0 を含むエントリ群から生成した場合、その params が継承される。
        let engine_with_slot0 = VaultEngine::from_slot_entries(core::slice::from_ref(&entry));
        assert_eq!(
            engine_with_slot0.dummy_argon2_params().m_cost(),
            custom_params.m_cost()
        );

        // Slot 0 を含まないエントリ群から生成した場合、default_for_target にフォールバックする。
        let prf_entry = wrap_dek_slot1(
            &dek,
            &[3u8; 32],
            &[4u8; SLOT1_SALT_LEN],
            &[5u8; SLOT1_NONCE_LEN],
            &header.associated_data(),
        )
        .expect("Slot 1 ラップに成功。");
        let engine_without_slot0 =
            VaultEngine::from_slot_entries(core::slice::from_ref(&prf_entry));
        assert_eq!(
            engine_without_slot0.dummy_argon2_params().m_cost(),
            Argon2Params::default_for_target().m_cost()
        );
    }

    #[test]
    fn test_vault_engine_dummy_argon2_params_consistent_on_invalid_or_missing_slot0() {
        let dek = test_dek();
        let custom_params = Argon2Params::fast_test().with_m_cost(128);
        let header = test_header();
        let entry = wrap_dek_slot0(
            &dek,
            b"test_password",
            &[1u8; SLOT0_SALT_LEN],
            &[2u8; SLOT0_NONCE_LEN],
            &custom_params,
            &header.associated_data(),
        )
        .expect("Slot 0 ラップに成功。");
        let vault = Vault::new(header, vec![entry], vec![]);

        // 1. スロット無効化状態のエンジンでも、Vault内のカスタムパラメータでダミー演算が実行される。
        let invalid_engine = VaultEngine::locked();
        let mut trace = SlotEvalTrace::default();
        let header_aad = vault.header.associated_data();
        let res = invalid_engine.eval_vault_credential_traced(
            &vault,
            SlotCredential::password(b"wrong_password"),
            &header_aad,
            &mut trace,
        );
        assert_eq!(res.err(), Some(VaultError::AuthenticationFailed));
        assert_eq!(trace.dummy_argon2id_ops, 1);
        assert_eq!(trace.real_argon2id_ops, 0);

        // 2. unlock_vault_with_all_slots で SlotKind::Argon2id が未提示の場合も同様にダミー演算が実行される。
        let mut all_slots_engine = VaultEngine::from_slot_entries(&vault.slots);
        let prf_cred = SlotCredential::prf(&[3u8; 32]);
        let (all_res, all_trace) =
            all_slots_engine.unlock_vault_with_any_traced(&vault, &[prf_cred], true);
        assert_eq!(all_res.err(), Some(VaultError::AuthenticationFailed));
        assert_eq!(all_trace.dummy_argon2id_ops, 1);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(32))]

        #[test]
        fn prop_slot0_wrap_unwrap_roundtrip(
            dek_bytes in any::<[u8; DEK_LEN]>(),
            password in prop::collection::vec(any::<u8>(), 0..64),
            salt in any::<[u8; SLOT0_SALT_LEN]>(),
            nonce in any::<[u8; SLOT0_NONCE_LEN]>(),
            vault_aad in prop::collection::vec(any::<u8>(), 0..64),
        ) {
            let dek = SecretBytes::new(dek_bytes);
            let params = test_params();
            let entry = wrap_dek_slot0(&dek, &password, &salt, &nonce, &params, &vault_aad)
                .expect("任意入力でのSlot 0ラップに成功。");
            let unwrapped = unwrap_dek_slot0(&entry, &password, &vault_aad)
                .expect("任意入力でのSlot 0復号に成功。");
            prop_assert_eq!(unwrapped.as_bytes(), dek.as_bytes());
        }

        #[test]
        fn prop_slot1_wrap_unwrap_roundtrip(
            dek_bytes in any::<[u8; DEK_LEN]>(),
            prf in prop::collection::vec(any::<u8>(), SLOT1_MIN_PRF_LEN..96),
            salt in any::<[u8; SLOT1_SALT_LEN]>(),
            nonce in any::<[u8; SLOT1_NONCE_LEN]>(),
            vault_aad in prop::collection::vec(any::<u8>(), 0..64),
        ) {
            let dek = SecretBytes::new(dek_bytes);
            // 任意長の有効な PRF 出力におけるラップ・復号の一致を確認。
            let entry = wrap_dek_slot1(&dek, &prf, &salt, &nonce, &vault_aad).unwrap();
            let unwrapped = unwrap_dek_slot1(&entry, &prf, &vault_aad).unwrap();
            prop_assert_eq!(unwrapped.as_bytes(), dek.as_bytes());
        }

        #[test]
        fn prop_slot2_wrap_unwrap_roundtrip(
            dek_bytes in any::<[u8; DEK_LEN]>(),
            secret in prop::collection::vec(any::<u8>(), SLOT2_MIN_SECRET_LEN..96),
            salt in any::<[u8; SLOT2_SALT_LEN]>(),
            nonce in any::<[u8; SLOT2_NONCE_LEN]>(),
            vault_aad in prop::collection::vec(any::<u8>(), 0..64),
        ) {
            let dek = SecretBytes::new(dek_bytes);
            // 任意長の高エントロピーシークレットにおけるラップ・復号の一致を確認。
            let entry = wrap_dek_slot2(&dek, &secret, &salt, &nonce, &vault_aad).unwrap();
            let unwrapped = unwrap_dek_slot2(&entry, &secret, &vault_aad).unwrap();
            prop_assert_eq!(unwrapped.as_bytes(), dek.as_bytes());
        }

        #[test]
        fn prop_slot0_from_bytes_never_panics(
            raw in prop::collection::vec(any::<u8>(), 0..256),
            slot_id in any::<u8>(),
            kdf_kind in any::<u8>(),
        ) {
            let _ = Argon2idSlotPayload::from_bytes(&raw);
            let _ = PrfSlotPayload::from_bytes(&raw);
            let _ = RecoverySlotPayload::from_bytes(&raw);
            let _ = normalize_recovery_code(&raw);
            if let Ok(entry) = KekSlotEntry::new(slot_id, kdf_kind, raw) {
                let _ = unwrap_dek_slot0(&entry, b"password", b"aad");
                let _ = unwrap_dek_slot1(&entry, &[0x42; SLOT1_MIN_PRF_LEN], b"aad");
                let _ = unwrap_dek_slot2(&entry, &[0x42; SLOT2_MIN_SECRET_LEN], b"aad");
            }
        }

        #[test]
        fn prop_smoothed_unlock_preserves_invariant_and_constant_op_counts(
            slot_modes in [0u8..4, 0u8..4, 0u8..4],
            cred_specs in prop::collection::vec((0u8..4, any::<bool>()), 1..=6),
            include_all in any::<bool>(),
        ) {
            // slot_modes[i]: 0=不在, 1=有効, 2=破損, 3=重複。
            let dek = test_dek();
            let header = test_header();
            let password = b"prop-master-pw";
            let prf = test_prf_secret();
            let recovery = test_recovery_secret();

            let valid_entries = [
                wrap_dek_slot0_for_header(&dek, password, &test_salt(), &test_nonce(), &test_params(), &header).unwrap(),
                wrap_dek_slot1_for_header(&dek, &prf, &test_salt32(), &test_nonce(), &header).unwrap(),
                wrap_dek_slot2_for_header(&dek, &recovery, &test_salt32(), &test_nonce(), &header).unwrap(),
            ];
            let kdf_kinds = [KDF_KIND_ARGON2ID, KDF_KIND_HKDF_SHA256, KDF_KIND_RECOVERY];

            let mut entries = alloc::vec::Vec::new();
            for idx in 0..3 {
                match slot_modes[idx] {
                    1 => entries.push(valid_entries[idx].clone()),
                    2 => entries.push(KekSlotEntry::new(idx as u8, kdf_kinds[idx], vec![0xAA; 12]).unwrap()),
                    3 => {
                        entries.push(valid_entries[idx].clone());
                        entries.push(valid_entries[idx].clone());
                    }
                    _ => {}
                }
            }

            let vault = Vault::new(header, entries, vec![]);
            let mut engine = VaultEngine::from_slot_entries(&vault.slots)
                .with_dummy_argon2_params(test_params());

            let wrong_pw = b"wrong-pw";
            let wrong_prf = [0x01u8; SLOT1_MIN_PRF_LEN];
            let wrong_rec = [0x02u8; SLOT2_MIN_SECRET_LEN];
            let mut expected_argon2_ops = 0usize;
            let mut expected_hkdf_ops = 0usize;
            let mut seen = [false; SlotKind::COUNT];
            let mut creds = alloc::vec::Vec::with_capacity(cred_specs.len());

            for &(kind_sel, use_valid_secret) in &cred_specs {
                match kind_sel {
                    0 => {
                        expected_argon2_ops += 1;
                        seen[0] = true;
                        creds.push(SlotCredential::password(if use_valid_secret {
                            password
                        } else {
                            wrong_pw
                        }));
                    }
                    1 => {
                        expected_hkdf_ops += 1;
                        seen[1] = true;
                        creds.push(SlotCredential::prf(if use_valid_secret {
                            &prf
                        } else {
                            &wrong_prf
                        }));
                    }
                    2 => {
                        expected_hkdf_ops += 1;
                        seen[2] = true;
                        creds.push(SlotCredential::recovery(if use_valid_secret {
                            &recovery
                        } else {
                            &wrong_rec
                        }));
                    }
                    _ => {
                        expected_hkdf_ops += 1;
                        seen[2] = true;
                        creds.push(SlotCredential::recovery_code(b"INVALID"));
                    }
                }
            }

            if include_all {
                if !seen[0] {
                    expected_argon2_ops += 1;
                }
                if !seen[1] {
                    expected_hkdf_ops += 1;
                }
                if !seen[2] {
                    expected_hkdf_ops += 1;
                }
            }

            let (res, trace) = engine.unlock_vault_with_any_traced(&vault, &creds, include_all);

            prop_assert_eq!(trace.argon2id_ops(), expected_argon2_ops);
            prop_assert_eq!(trace.hkdf_ops(), expected_hkdf_ops);
            prop_assert_eq!(trace.total_kdf_ops(), expected_argon2_ops + expected_hkdf_ops);
            prop_assert_eq!(trace.total_aead_ops(), expected_argon2_ops + expected_hkdf_ops);
            prop_assert!(engine.is_safe_state());

            match res {
                Ok(kind) => {
                    prop_assert_eq!(engine.state(), VaultState::Unlocked);
                    prop_assert_eq!(slot_modes[kind.as_slot_id() as usize], 1);
                    prop_assert_eq!(engine.dek().unwrap().as_bytes(), dek.as_bytes());
                }
                Err(_) => {
                    prop_assert_eq!(engine.state(), VaultState::Locked);
                    prop_assert!(engine.observe_dek().is_none());
                }
            }
        }

        #[test]
        fn prop_external_unlock_non_interference_error_uniformity(
            slot_modes_a in [0u8..4, 0u8..4, 0u8..4],
            slot_modes_b in [0u8..4, 0u8..4, 0u8..4],
            cred_kind in 0u8..4,
            include_all in any::<bool>(),
        ) {
            // 任意の2つのスロット構成 A, B (不在, 有効, 破損, 重複の任意の組み合わせ) に対し、
            // 認証失敗時に外部公開API境界から観測されるエラー型は常に単一の AuthenticationFailed であり、
            // スロットの有無や破損状態の差異が一切漏洩しないことを検証する。
            let dek = test_dek();
            let header = test_header();
            let valid_entries = [
                wrap_dek_slot0_for_header(&dek, b"right-pw", &test_salt(), &test_nonce(), &test_params(), &header).unwrap(),
                wrap_dek_slot1_for_header(&dek, &test_prf_secret(), &test_salt32(), &test_nonce(), &header).unwrap(),
                wrap_dek_slot2_for_header(&dek, &test_recovery_secret(), &test_salt32(), &test_nonce(), &header).unwrap(),
            ];
            let kdf_kinds = [KDF_KIND_ARGON2ID, KDF_KIND_HKDF_SHA256, KDF_KIND_RECOVERY];

            let build_vault = |modes: [u8; 3]| -> Vault {
                let mut entries = alloc::vec::Vec::new();
                for idx in 0..3 {
                    match modes[idx] {
                        1 => entries.push(valid_entries[idx].clone()),
                        2 => entries.push(KekSlotEntry::new(idx as u8, kdf_kinds[idx], vec![0xAA; 12]).unwrap()),
                        3 => {
                            entries.push(valid_entries[idx].clone());
                            entries.push(valid_entries[idx].clone());
                        }
                        _ => {}
                    }
                }
                Vault::new(header, entries, vec![])
            };

            let vault_a = build_vault(slot_modes_a);
            let vault_b = build_vault(slot_modes_b);
            let mut engine_a = VaultEngine::from_slot_entries(&vault_a.slots).with_dummy_argon2_params(test_params());
            let mut engine_b = VaultEngine::from_slot_entries(&vault_b.slots).with_dummy_argon2_params(test_params());

            let wrong_prf = [0x01u8; SLOT1_MIN_PRF_LEN];
            let wrong_rec = [0x02u8; SLOT2_MIN_SECRET_LEN];
            let cred = match cred_kind {
                0 => SlotCredential::password(b"wrong-pw"),
                1 => SlotCredential::prf(&wrong_prf),
                2 => SlotCredential::recovery(&wrong_rec),
                _ => SlotCredential::recovery_code(b"SHORT!"),
            };

            let err_single_a = engine_a.unlock_vault_with_credential(&vault_a, cred);
            let err_single_b = engine_b.unlock_vault_with_credential(&vault_b, cred);
            prop_assert_eq!(err_single_a, Err(VaultError::AuthenticationFailed));
            prop_assert_eq!(err_single_a, err_single_b);

            let err_multi_a = if include_all {
                engine_a.unlock_vault_with_all_slots(&vault_a, &[cred])
            } else {
                engine_a.unlock_vault_with_any(&vault_a, &[cred])
            };
            let err_multi_b = if include_all {
                engine_b.unlock_vault_with_all_slots(&vault_b, &[cred])
            } else {
                engine_b.unlock_vault_with_any(&vault_b, &[cred])
            };
            prop_assert_eq!(err_multi_a, Err(VaultError::AuthenticationFailed));
            prop_assert_eq!(err_multi_a, err_multi_b);
            prop_assert!(engine_a.is_safe_state());
            prop_assert!(engine_b.is_safe_state());
        }
    }

    #[test]
    fn test_aad_buffer_stack_and_heap_behavior() {
        // スタック容量以下の場合はスタックバリアント。
        let mut buf_stack: AadBuffer<16> = AadBuffer::new(10);
        assert!(buf_stack.is_stack());
        buf_stack.push(0x01);
        buf_stack.extend_from_slice(&[0x02, 0x03, 0x04]);
        assert_eq!(buf_stack.as_slice(), &[0x01, 0x02, 0x03, 0x04]);
        assert_eq!(&*buf_stack, &[0x01, 0x02, 0x03, 0x04]);

        // スタック容量超過時はヒープバリアントへフォールバック。
        let mut buf_heap: AadBuffer<16> = AadBuffer::new(20);
        assert!(!buf_heap.is_stack());
        buf_heap.push(0xAA);
        buf_heap.extend_from_slice(&[0xBB, 0xCC]);
        assert_eq!(buf_heap.as_slice(), &[0xAA, 0xBB, 0xCC]);

        // デフォルト構築は空のスタックバリアント。
        let default_buf: AadBuffer<16> = AadBuffer::default();
        assert!(default_buf.is_stack());
        assert!(default_buf.is_empty());
    }

    #[test]
    fn test_slot0_aad_zero_allocation_and_fallback() {
        let params = test_params();
        let salt = test_salt();
        let header = test_header();
        let header_aad = header.associated_data();

        // 通常の VaultHeader AAD (14B) バインド時はスタック完結 (ゼロアロケーション)。
        let aad_normal = build_slot0_aad(&params, &salt, &header_aad).unwrap();
        assert!(aad_normal.is_stack());
        assert_eq!(aad_normal.len(), SLOT0_AAD_FIXED_LEN + VAULT_HEADER_LEN);
        assert_eq!(aad_normal.len(), 62);
        assert!(aad_normal.starts_with(SLOT0_AAD_PREFIX));
        assert_eq!(aad_normal[18], SLOT_ID_ARGON2ID);
        assert_eq!(aad_normal[19], KDF_KIND_ARGON2ID);
        assert_eq!(&aad_normal[62 - VAULT_HEADER_LEN..], &header_aad);

        // 空 AAD 時もスタック完結。
        let aad_empty = build_slot0_aad(&params, &salt, &[]).unwrap();
        assert!(aad_empty.is_stack());
        assert_eq!(aad_empty.len(), SLOT0_AAD_FIXED_LEN);

        // スタック上限 (64B) を超過する大規模 AAD ではヒープへフォールバック。
        let large_aad = [0x77u8; 100];
        let aad_large = build_slot0_aad(&params, &salt, &large_aad).unwrap();
        assert!(!aad_large.is_stack());
        assert_eq!(aad_large.len(), SLOT0_AAD_FIXED_LEN + 100);
        assert_eq!(&aad_large[SLOT0_AAD_FIXED_LEN..], &large_aad);
    }

    #[test]
    fn test_hkdf_slot_aad_zero_allocation_and_fallback() {
        let spec = SLOT1_SPEC;
        let salt = [0x42u8; SLOT1_SALT_LEN];
        let header = test_header();
        let header_aad = header.associated_data();

        // 通常の VaultHeader AAD (14B) バインド時はスタック完結 (ゼロアロケーション)。
        let aad_normal = build_hkdf_slot_aad(&spec, &salt, &header_aad).unwrap();
        assert!(aad_normal.is_stack());
        assert_eq!(aad_normal.len(), HKDF_SLOT_AAD_FIXED_LEN + VAULT_HEADER_LEN);
        assert_eq!(aad_normal.len(), 66);
        assert!(aad_normal.starts_with(spec.aad_prefix));
        assert_eq!(aad_normal[18], spec.slot_id);
        assert_eq!(aad_normal[19], spec.kdf_kind);
        assert_eq!(&aad_normal[66 - VAULT_HEADER_LEN..], &header_aad);

        // 空 AAD 時もスタック完結。
        let aad_empty = build_hkdf_slot_aad(&spec, &salt, &[]).unwrap();
        assert!(aad_empty.is_stack());
        assert_eq!(aad_empty.len(), HKDF_SLOT_AAD_FIXED_LEN);

        // スタック上限 (68B) を超過する大規模 AAD ではヒープへフォールバック。
        let large_aad = [0x88u8; 100];
        let aad_large = build_hkdf_slot_aad(&spec, &salt, &large_aad).unwrap();
        assert!(!aad_large.is_stack());
        assert_eq!(aad_large.len(), HKDF_SLOT_AAD_FIXED_LEN + 100);
        assert_eq!(&aad_large[HKDF_SLOT_AAD_FIXED_LEN..], &large_aad);
    }
}
