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

use crate::cipher::{
    CipherSuiteId, MAX_AAD_LEN, TAG_LEN, VaultCipher, XCHACHA20_POLY1305_NONCE_LEN,
};
use crate::envelope::{DEK_LEN, KekSlots, SLOT_ID_ARGON2ID, SlotKind, SlotStatus, VaultEngine};
use crate::error::{CryptoError, TlvParseError, VaultError};
use crate::kdf::Argon2Params;
use crate::tlv::{KekSlotEntry, Vault, VaultHeader};
use crate::zeroize::{SecretBytes, volatile_zeroize};

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

        let m_cost = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let t_cost = u32::from_be_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        let p_cost = u32::from_be_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]);

        let params = Argon2Params::custom(m_cost, t_cost, p_cost, Some(DEK_LEN))?;
        validate_slot0_argon2_params(&params)?;

        let mut salt = [0u8; SLOT0_SALT_LEN];
        salt.copy_from_slice(&bytes[12..28]);

        let mut nonce = [0u8; SLOT0_NONCE_LEN];
        nonce.copy_from_slice(&bytes[28..52]);

        let mut ciphertext = [0u8; SLOT0_CIPHERTEXT_LEN];
        ciphertext.copy_from_slice(&bytes[52..84]);

        let mut auth_tag = [0u8; SLOT0_TAG_LEN];
        auth_tag.copy_from_slice(&bytes[84..100]);

        Ok(Self {
            params,
            salt,
            nonce,
            ciphertext,
            auth_tag,
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

/// Slot 0 の暗号化および復号に用いる AEAD 関連データ (AAD) を構築する。
///
/// ドメイン分離プレフィックス, スロット識別子, KDF 種別, Argon2id パラメータ,
/// ソルト, 呼び出し元が指定した `vault_aad` (通常は [`VaultHeader::associated_data`]) を結合し、
/// パラメータのダウングレード攻撃やヘッダーとスロットの間のすり替えを検知する。
fn build_slot0_aad(
    params: &Argon2Params,
    salt: &[u8; SLOT0_SALT_LEN],
    vault_aad: &[u8],
) -> Result<alloc::vec::Vec<u8>, CryptoError> {
    let total_len = SLOT0_AAD_FIXED_LEN
        .checked_add(vault_aad.len())
        .ok_or(CryptoError::InvalidSliceLength)?;
    if total_len > MAX_AAD_LEN {
        return Err(CryptoError::InvalidSliceLength);
    }

    let mut aad = alloc::vec::Vec::with_capacity(total_len);
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
    let cipher = VaultCipher::new_from_secret(SLOT_CIPHER_SUITE, &kek);
    volatile_zeroize(kek.as_mut_slice());

    let mut work_buf = SecretBytes::new(*dek.as_bytes());
    let encrypt_res = cipher.encrypt_in_place_detached(nonce, &aad, work_buf.as_mut_slice());
    let auth_tag = match encrypt_res {
        Ok(tag) => tag,
        Err(err) => {
            volatile_zeroize(work_buf.as_mut_slice());
            return Err(VaultError::Crypto(err));
        }
    };

    let payload = Argon2idSlotPayload {
        params: *params,
        salt: *salt,
        nonce: *nonce,
        ciphertext: *work_buf.as_bytes(),
        auth_tag,
    };
    volatile_zeroize(work_buf.as_mut_slice());

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
    let cipher = VaultCipher::new_from_secret(SLOT_CIPHER_SUITE, &kek);
    volatile_zeroize(kek.as_mut_slice());

    let mut dek = SecretBytes::new(payload.ciphertext);
    if let Err(err) = cipher.decrypt_in_place_detached_tag(
        &payload.nonce,
        &aad,
        dek.as_mut_slice(),
        &payload.auth_tag,
    ) {
        volatile_zeroize(dek.as_mut_slice());
        return Err(VaultError::Crypto(err));
    }

    Ok(dek)
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
/// 各スロット ID (`0`, `1`, `2`) について未設定, 有効, 無効(または重複)を判定する。
/// Slot 0 についてはフォーマット長, KDF 種別, Argon2id パラメータの境界まで検証する。
#[must_use]
pub fn inspect_kek_slots(entries: &[KekSlotEntry]) -> KekSlots {
    let mut slots = KekSlots::unset_all();
    let mut seen = [false; 3];

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
                if entry.kdf_kind() == KDF_KIND_HKDF_SHA256 && !entry.wrapped_dek().is_empty() {
                    SlotStatus::Valid
                } else {
                    SlotStatus::Invalid
                }
            }
            SlotKind::Recovery => {
                if entry.kdf_kind() == KDF_KIND_RECOVERY && !entry.wrapped_dek().is_empty() {
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

impl VaultEngine {
    /// TLV の [`KekSlotEntry`] 一覧を検証し、施錠状態の新しい [`VaultEngine`] を生成する。
    #[must_use]
    pub fn from_slot_entries(entries: &[KekSlotEntry]) -> Self {
        Self::new(inspect_kek_slots(entries))
    }

    /// Slot 0 (Argon2id マスターパスワード) エントリを用いて解錠パイプラインを実行する。
    ///
    /// `Locked -> Unlocking -> Unlocked` の状態遷移を厳密に制御し、
    /// 復号失敗時は即座に [`VaultEngine::fail_unlock`] で `Locked` へ復帰し、安全状態の不変条件を保つ。
    ///
    /// # 前提条件
    ///
    /// 現在の状態が [`crate::envelope::VaultState::Locked`] であり、
    /// かつ本エンジン上で Slot 0 が [`SlotStatus::Valid`] として登録されている必要がある。
    ///
    /// # Errors
    ///
    /// - 現在の状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - Slot 0 が `Valid` でない場合は [`VaultError::AuthenticationFailed`] を返す。
    /// - フォーマット検証, 鍵導出, AEAD 復号のいずれかに失敗した場合は対応する [`VaultError`] を返す。
    pub fn unlock_with_slot0(
        &mut self,
        entry: &KekSlotEntry,
        password: &[u8],
        vault_aad: &[u8],
    ) -> Result<(), VaultError> {
        self.unlock_with_slot0_with_secret(entry, password, &[], vault_aad)
    }

    /// ペッパー (`secret`) を併用し、Slot 0 エントリによる解錠パイプラインを実行する。
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
        self.start_unlock(SLOT_ID_ARGON2ID)?;

        if !self.slots().is_slot_valid(SLOT_ID_ARGON2ID) {
            let _ = self.fail_unlock();
            return Err(VaultError::AuthenticationFailed);
        }

        match unwrap_dek_slot0_with_secret(entry, password, secret, vault_aad) {
            Ok(dek) => {
                if let Err(err) = self.complete_unlock(SLOT_ID_ARGON2ID, dek) {
                    let _ = self.fail_unlock();
                    return Err(err);
                }
                Ok(())
            }
            Err(err) => {
                let _ = self.fail_unlock();
                Err(err)
            }
        }
    }

    /// [`Vault`] コンテナ全体から Slot 0 を検索し、Vault ヘッダー AAD をバインドして解錠する。
    ///
    /// # Errors
    ///
    /// - 状態が `Locked` でない場合は [`VaultError::InvalidState`] を返す。
    /// - Slot 0 が存在しない場合は [`VaultError::SlotNotFound`]、重複時は [`VaultError::Parse`] を返す。
    /// - 認証または復号に失敗した場合は対応する [`VaultError`] を返す。
    pub fn unlock_vault_with_password(
        &mut self,
        vault: &Vault,
        password: &[u8],
    ) -> Result<(), VaultError> {
        if !self.state().is_locked() {
            return Err(VaultError::InvalidState);
        }
        let slot0 = find_slot_entry(&vault.slots, SLOT_ID_ARGON2ID)?;
        let header_aad = vault.header.associated_data();
        self.unlock_with_slot0(slot0, password, &header_aad)
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::envelope::{SLOT_ID_PRF, SLOT_ID_RECOVERY, VaultState};
    use crate::tlv::{EntryPayload, TlvRecord, VAULT_MAGIC, deserialize, serialize};
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

        // 誤パスワードでの失敗時は Unlocking -> Locked に復帰し SafeState を維持する。
        assert_eq!(
            engine.unlock_vault_with_password(&parsed_vault, b"wrong-pass"),
            Err(VaultError::Crypto(CryptoError::AeadDecryptionFailed))
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
        fn prop_slot0_from_bytes_never_panics(
            raw in prop::collection::vec(any::<u8>(), 0..256),
            slot_id in any::<u8>(),
            kdf_kind in any::<u8>(),
        ) {
            let _ = Argon2idSlotPayload::from_bytes(&raw);
            if let Ok(entry) = KekSlotEntry::new(slot_id, kdf_kind, raw) {
                let _ = unwrap_dek_slot0(&entry, b"password", b"aad");
            }
        }
    }
}
