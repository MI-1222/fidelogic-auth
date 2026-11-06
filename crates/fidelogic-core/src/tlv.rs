//! # 最小限のゼロコピーTLVパーサー
//!
//! Charon / Aeneas 形式検証ターゲット用の純粋関数型パースロジック。

#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct TlvHeader {
    pub tag: u8,
    pub length: u8,
}

/// TLVレコードヘッダーのバイト長(2バイト: Tag 1B + Length 1B)。
pub const TLV_HEADER_LEN: usize = 2;

/// 2バイトのヘッダー [Tag (1B), Length (1B)] を安全に取得する。
#[must_use]
pub fn parse_tlv_header(bytes: &[u8]) -> Option<TlvHeader> {
    if bytes.len() < TLV_HEADER_LEN {
        None
    } else {
        Some(TlvHeader {
            tag: bytes[0],
            length: bytes[1],
        })
    }
}

/// ヘッダーおよびペイロード境界の健全性を検証する。
#[must_use]
pub fn validate_tlv_bounds(bytes: &[u8]) -> bool {
    if let Some(header) = parse_tlv_header(bytes) {
        let required_len = TLV_HEADER_LEN + (header.length as usize);
        bytes.len() >= required_len
    } else {
        false
    }
}

/// Vaultヘッダーの既定マジックバイト。
pub const VAULT_MAGIC: [u8; 4] = *b"FVAU";

/// Vaultヘッダーのバイト長(6バイト)。
pub const VAULT_HEADER_LEN: usize = 6;

/// Vaultバイナリフォーマットの固定長ヘッダー。
///
/// マジックバイト, フォーマットバージョン, 暗号スイートID を保持する。
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct VaultHeader {
    /// マジックバイト(4バイト)。
    pub magic: [u8; 4],
    /// フォーマットバージョン。
    pub version: u8,
    /// 暗号スイート識別子。
    pub suite_id: u8,
}

/// `VaultHeader` 単体の純粋関数型デシリアライザー。
///
/// 入力バイト列からヘッダー情報 (マジックバイト, バージョン, 暗号スイートID) を安全に読み取り、
/// デシリアライズされた [`VaultHeader`] と残余バイトスライスを返す。
///
/// # Errors
///
/// - 入力バイト列の長さがヘッダー長 ([`VAULT_HEADER_LEN`]) 未満の場合は [`VaultError::UnexpectedEof`] を返す。
/// - マジックバイトが [`VAULT_MAGIC`] と一致しない場合は [`VaultError::InvalidMagic`] を返す。
pub fn deserialize_header(bytes: &[u8]) -> Result<(VaultHeader, &[u8]), TlvParseError> {
    if bytes.len() < VAULT_HEADER_LEN {
        return Err(VaultError::UnexpectedEof);
    }
    let magic = [bytes[0], bytes[1], bytes[2], bytes[3]];
    if magic != VAULT_MAGIC {
        return Err(VaultError::InvalidMagic);
    }
    let version = bytes[4];
    let suite_id = bytes[5];
    let header = VaultHeader {
        magic,
        version,
        suite_id,
    };
    Ok((header, &bytes[VAULT_HEADER_LEN..]))
}

/// `VaultHeader` 単体の純粋関数型シリアライザー。
///
/// 指定された [`VaultHeader`] を固定長バイト配列 (6バイト) にシリアライズする。
#[must_use]
pub const fn serialize_header(header: &VaultHeader) -> [u8; VAULT_HEADER_LEN] {
    [
        header.magic[0],
        header.magic[1],
        header.magic[2],
        header.magic[3],
        header.version,
        header.suite_id,
    ]
}

/// VaultおよびTLVパース処理で発生するエラーを表す列挙型。
///
/// パニックを完全に排除し、境界外アクセスや不正なフォーマットを純粋な値として通知する。
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum VaultError {
    /// 入力バイト列の長さが不足している。
    UnexpectedEof,
    /// マジックバイトが既定値と一致しない。
    InvalidMagic,
    /// 未知または非対応のフォーマットバージョン。
    UnsupportedVersion,
    /// 未知または非対応の暗号スイートID。
    UnsupportedSuite,
    /// 宣言されたデータ長が不正またはスライス境界を超過している。
    InvalidLength,
    /// レコードまたはヘッダーのフォーマットが不正。
    InvalidFormat,
}

/// TLVパース専用のエラー型エイリアス。
pub type TlvParseError = VaultError;

/// KEKスロットヘッダーのバイト長(4バイト)。
pub const KEK_SLOT_HEADER_LEN: usize = 4;

/// KEKスロットヘッダー長の後方互換用エイリアス(4バイト)。
pub const KEK_SLOT_ENTRY_LEN: usize = KEK_SLOT_HEADER_LEN;

/// KEKスロット定義テーブルのエントリを表すレコード。
///
/// スロットID, KDF種別, ラップ済みDEKのバイト長, および暗号化DEK本体(Wrapped DEK)を保持する。
#[cfg(feature = "alloc")]
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
pub struct KekSlotEntry {
    /// スロット識別子。
    pub slot_id: u8,
    /// 鍵導出関数(KDF)の種別。
    pub kdf_kind: u8,
    /// ラップ済みDEKのバイト長。
    pub wrapped_dek_len: u16,
    /// 暗号化DEK本体(Wrapped DEK)。
    pub wrapped_dek: alloc::vec::Vec<u8>,
}

#[cfg(feature = "alloc")]
impl KekSlotEntry {
    /// 新しいKEKスロットエントリ構造体を生成する。
    ///
    /// # Errors
    ///
    /// - `wrapped_dek` のバイト長が `u16::MAX` を超過する場合は [`VaultError::InvalidLength`] を返す。
    pub fn new(
        slot_id: u8,
        kdf_kind: u8,
        wrapped_dek: alloc::vec::Vec<u8>,
    ) -> Result<Self, VaultError> {
        let wrapped_dek_len =
            u16::try_from(wrapped_dek.len()).map_err(|_| VaultError::InvalidLength)?;
        Ok(Self {
            slot_id,
            kdf_kind,
            wrapped_dek_len,
            wrapped_dek,
        })
    }
}

/// `KekSlotEntry` 単体の純粋関数型デシリアライザー。
///
/// 入力バイト列からスロットID (1B), KDF種別 (1B), ラップ済みDEK長 (2B, ビッグエンディアン),
/// およびラップ済みDEK実体データを安全に読み取り、
/// デシリアライズされた [`KekSlotEntry`] と残余バイトスライスを返す。
///
/// # Errors
///
/// - 入力バイト列の長さがヘッダー長 ([`KEK_SLOT_HEADER_LEN`]) 未満の場合は [`VaultError::UnexpectedEof`] を返す。
/// - 入力バイト列の長さがヘッダー長とラップ済みDEK長の合計未満の場合は [`VaultError::UnexpectedEof`] を返す。
#[cfg(feature = "alloc")]
pub fn deserialize_slot_entry(bytes: &[u8]) -> Result<(KekSlotEntry, &[u8]), TlvParseError> {
    if bytes.len() < KEK_SLOT_HEADER_LEN {
        return Err(VaultError::UnexpectedEof);
    }
    let slot_id = bytes[0];
    let kdf_kind = bytes[1];
    let wrapped_dek_len = u16::from_be_bytes([bytes[2], bytes[3]]);
    let dek_len = wrapped_dek_len as usize;

    let payload_bytes = &bytes[KEK_SLOT_HEADER_LEN..];
    if payload_bytes.len() < dek_len {
        return Err(VaultError::UnexpectedEof);
    }

    let wrapped_dek = payload_bytes[..dek_len].to_vec();
    let entry = KekSlotEntry {
        slot_id,
        kdf_kind,
        wrapped_dek_len,
        wrapped_dek,
    };
    Ok((entry, &payload_bytes[dek_len..]))
}

/// `KekSlotEntry` 単体の純粋関数型シリアライザー。
///
/// 指定された [`KekSlotEntry`] をバイナリ形式にシリアライズする。
/// スロットID (1B), KDF種別 (1B), ラップ済みDEK長 (2B, ビッグエンディアン),
/// および暗号化DEK本体(Wrapped DEK)のバイト列を出力する。
///
/// # Errors
///
/// - `wrapped_dek` の実体長と `wrapped_dek_len` が一致しない場合は [`VaultError::InvalidLength`] を返す。
/// - `wrapped_dek` の実体長が `u16::MAX` を超過する場合は [`VaultError::InvalidLength`] を返す。
#[cfg(feature = "alloc")]
pub fn serialize_slot_entry(entry: &KekSlotEntry) -> Result<alloc::vec::Vec<u8>, VaultError> {
    if entry.wrapped_dek.len() > u16::MAX as usize {
        return Err(VaultError::InvalidLength);
    }
    if entry.wrapped_dek.len() != entry.wrapped_dek_len as usize {
        return Err(VaultError::InvalidLength);
    }
    let len_bytes = entry.wrapped_dek_len.to_be_bytes();
    let mut bytes = alloc::vec::Vec::with_capacity(KEK_SLOT_HEADER_LEN + entry.wrapped_dek.len());
    bytes.push(entry.slot_id);
    bytes.push(entry.kdf_kind);
    bytes.push(len_bytes[0]);
    bytes.push(len_bytes[1]);
    bytes.extend_from_slice(&entry.wrapped_dek);
    Ok(bytes)
}

/// AEAD認証タグのバイト長(16バイト)。
pub const AUTH_TAG_LEN: usize = 16;

/// エントリレコードの既知タグ(1)。
pub const TAG_ENTRY: u8 = 1;

/// 指定されたタグが既知のレコード種別であるかを判定する。
#[must_use]
pub const fn is_known_tag(tag: u8) -> bool {
    tag == TAG_ENTRY
}

/// TLVレコードの既知ペイロード(暗号化データおよび認証タグ)。
#[cfg(feature = "alloc")]
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
pub struct TlvPayload {
    /// 暗号化データ本体。
    pub ciphertext: alloc::vec::Vec<u8>,
    /// AEAD認証タグ(16バイト)。
    pub auth_tag: [u8; AUTH_TAG_LEN],
}

#[cfg(feature = "alloc")]
impl TlvPayload {
    /// 新しい既知ペイロード構造体を生成する。
    #[must_use]
    pub fn new(ciphertext: alloc::vec::Vec<u8>, auth_tag: [u8; AUTH_TAG_LEN]) -> Self {
        Self {
            ciphertext,
            auth_tag,
        }
    }
}

/// ペイロード部のTLVレコードを表す列挙型。
///
/// 既知タグ(`Known`)または将来拡張用の未知タグ(`UnknownTag`)を表現する。
#[cfg(feature = "alloc")]
#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
pub enum TlvRecord {
    /// 既知タグと解釈済みペイロード。
    Known {
        /// レコード種別タグ。
        tag: u8,
        /// 暗号化データおよび認証タグ。
        payload: TlvPayload,
    },
    /// 未知タグと未解釈生バイト列。
    UnknownTag {
        /// レコード種別タグ。
        tag: u8,
        /// レコードの生バイト列。
        raw_bytes: alloc::vec::Vec<u8>,
    },
}

#[cfg(feature = "alloc")]
impl PartialEq for TlvRecord {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Known {
                    tag: tag1,
                    payload: payload1,
                },
                Self::Known {
                    tag: tag2,
                    payload: payload2,
                },
            ) => tag1 == tag2 && payload1 == payload2,
            (
                Self::UnknownTag {
                    tag: tag1,
                    raw_bytes: bytes1,
                },
                Self::UnknownTag {
                    tag: tag2,
                    raw_bytes: bytes2,
                },
            ) => tag1 == tag2 && bytes1 == bytes2,
            _ => false,
        }
    }
}

#[cfg(feature = "alloc")]
impl Eq for TlvRecord {}

#[cfg(feature = "alloc")]
impl TlvRecord {
    /// レコード種別タグを返す。
    #[must_use]
    pub const fn tag(&self) -> u8 {
        match *self {
            Self::Known { tag, .. } | Self::UnknownTag { tag, .. } => tag,
        }
    }
}

/// `TlvRecord` 単体の純粋関数型デシリアライザー。
///
/// 入力バイト列からヘッダー `[Tag (1B), Length (1B)]` を安全に取得し、
/// 続くペイロードバイト列を解釈する。
/// 既知タグ ([`TAG_ENTRY`]) の場合は暗号化データと認証タグ ([`AUTH_TAG_LEN`]) に分解して [`TlvRecord::Known`] を生成する。
/// 未知タグに遭遇した場合は、後続バイト列の安全な読み飛ばしを行い、生バイト列を保持する [`TlvRecord::UnknownTag`] を生成する。
/// デシリアライズされた [`TlvRecord`] と残余バイトスライスを返す。
///
/// # Errors
///
/// - 入力バイト列の長さがヘッダー長 (2バイト) 未満、または宣言長に満たない場合は [`VaultError::UnexpectedEof`] を返す。
/// - 既知タグのペイロード長が認証タグ長 ([`AUTH_TAG_LEN`]) 未満の場合は [`VaultError::InvalidLength`] を返す。
#[cfg(feature = "alloc")]
pub fn deserialize_record(bytes: &[u8]) -> Result<(TlvRecord, &[u8]), TlvParseError> {
    let Some(header) = parse_tlv_header(bytes) else {
        return Err(VaultError::UnexpectedEof);
    };
    let length = header.length as usize;
    let total_len = 2 + length;
    if bytes.len() < total_len {
        return Err(VaultError::UnexpectedEof);
    }
    let payload_bytes = &bytes[2..total_len];
    let rest = &bytes[total_len..];

    let record = if is_known_tag(header.tag) {
        if payload_bytes.len() < AUTH_TAG_LEN {
            return Err(VaultError::InvalidLength);
        }
        let ciphertext_len = payload_bytes.len() - AUTH_TAG_LEN;
        let ciphertext = alloc::vec::Vec::from(&payload_bytes[..ciphertext_len]);
        let mut auth_tag = [0u8; AUTH_TAG_LEN];
        auth_tag.copy_from_slice(&payload_bytes[ciphertext_len..]);
        TlvRecord::Known {
            tag: header.tag,
            payload: TlvPayload::new(ciphertext, auth_tag),
        }
    } else {
        let raw_bytes = alloc::vec::Vec::from(payload_bytes);
        TlvRecord::UnknownTag {
            tag: header.tag,
            raw_bytes,
        }
    };

    Ok((record, rest))
}

/// `TlvRecord` 単体の純粋関数型シリアライザー。
///
/// 指定された [`TlvRecord`] をバイト列にシリアライズする。
/// 既知レコードの場合は `[Tag (1B), Length (1B), Ciphertext..., AuthTag (16B)]`、
/// 未知レコードの場合は `[Tag (1B), Length (1B), RawBytes...]` を出力する。
///
/// # Errors
///
/// - ペイロード長が `u8::MAX` (255バイト) を超過する場合は [`VaultError::InvalidLength`] を返す。
#[cfg(feature = "alloc")]
pub fn serialize_record(record: &TlvRecord) -> Result<alloc::vec::Vec<u8>, VaultError> {
    match record {
        TlvRecord::Known { tag, payload } => {
            let payload_len = payload
                .ciphertext
                .len()
                .checked_add(AUTH_TAG_LEN)
                .ok_or(VaultError::InvalidLength)?;
            if payload_len > u8::MAX as usize {
                return Err(VaultError::InvalidLength);
            }
            let length = payload_len as u8;
            let mut bytes = alloc::vec::Vec::with_capacity(2 + payload_len);
            bytes.push(*tag);
            bytes.push(length);
            bytes.extend_from_slice(&payload.ciphertext);
            bytes.extend_from_slice(&payload.auth_tag);
            Ok(bytes)
        }
        TlvRecord::UnknownTag { tag, raw_bytes } => {
            if raw_bytes.len() > u8::MAX as usize {
                return Err(VaultError::InvalidLength);
            }
            let length = raw_bytes.len() as u8;
            let mut bytes = alloc::vec::Vec::with_capacity(2 + raw_bytes.len());
            bytes.push(*tag);
            bytes.push(length);
            bytes.extend_from_slice(raw_bytes);
            Ok(bytes)
        }
    }
}

/// Vault全体の集約型。
///
/// ヘッダー情報、KEKスロット定義テーブル、TLVレコード群を統括する。
#[cfg(feature = "alloc")]
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
pub struct Vault {
    /// Vaultヘッダー情報。
    pub header: VaultHeader,
    /// KEKスロット定義テーブル。
    pub slots: alloc::vec::Vec<KekSlotEntry>,
    /// TLVレコード群。
    pub records: alloc::vec::Vec<TlvRecord>,
}

#[cfg(feature = "alloc")]
impl Vault {
    /// 新しいVault構造体を生成する。
    #[must_use]
    pub fn new(
        header: VaultHeader,
        slots: alloc::vec::Vec<KekSlotEntry>,
        records: alloc::vec::Vec<TlvRecord>,
    ) -> Self {
        Self {
            header,
            slots,
            records,
        }
    }
}

/// `Vault` 全体の純粋関数型デシリアライザー。
///
/// 入力バイト列から [`VaultHeader`]、KEKスロット定義テーブル、およびTLVレコード群を順次デシリアライズし、
/// 結合された [`Vault`] と残余バイトスライスを返す。
///
/// # Errors
///
/// - 入力バイト列の長さが各フィールドの必要長に満たない場合は [`VaultError::UnexpectedEof`] を返す。
/// - スロット数やレコード数に対して残余バイト列長が不足している場合は [`VaultError::UnexpectedEof`] を返す。
/// - マジックバイトが不正な場合は [`VaultError::InvalidMagic`] を返す。
/// - レコード長や認証タグ長が不正な場合は各 [`VaultError`] を返す。
#[cfg(feature = "alloc")]
pub fn deserialize(bytes: &[u8]) -> Result<(Vault, &[u8]), TlvParseError> {
    let (header, mut rest) = deserialize_header(bytes)?;

    if rest.is_empty() {
        return Err(VaultError::UnexpectedEof);
    }
    let slot_count = rest[0] as usize;
    rest = &rest[1..];

    if slot_count.saturating_mul(KEK_SLOT_HEADER_LEN) > rest.len() {
        return Err(VaultError::UnexpectedEof);
    }

    let mut slots = alloc::vec::Vec::with_capacity(slot_count);
    for _ in 0..slot_count {
        let (slot_entry, next_rest) = deserialize_slot_entry(rest)?;
        slots.push(slot_entry);
        rest = next_rest;
    }

    if rest.len() < 2 {
        return Err(VaultError::UnexpectedEof);
    }
    let record_count = u16::from_be_bytes([rest[0], rest[1]]) as usize;
    rest = &rest[2..];

    if record_count.saturating_mul(TLV_HEADER_LEN) > rest.len() {
        return Err(VaultError::UnexpectedEof);
    }

    let mut records = alloc::vec::Vec::with_capacity(record_count);
    for _ in 0..record_count {
        let (record, next_rest) = deserialize_record(rest)?;
        records.push(record);
        rest = next_rest;
    }

    let vault = Vault::new(header, slots, records);
    Ok((vault, rest))
}

/// `Vault` 全体の純粋関数型シリアライザー。
///
/// 指定された [`Vault`] をバイナリ形式にシリアライズする。
/// ヘッダー、KEKスロット定義テーブル、およびTLVレコード群を結合したバイト列を出力する。
///
/// # Errors
///
/// - KEKスロット数が `u8::MAX` (255個) を超過する場合は [`VaultError::InvalidLength`] を返す。
/// - レコード数が `u16::MAX` (65535個) を超過する場合は [`VaultError::InvalidLength`] を返す。
/// - レコードシリアライズ処理でエラーが発生した場合はその [`VaultError`] を返す。
#[cfg(feature = "alloc")]
pub fn serialize(vault: &Vault) -> Result<alloc::vec::Vec<u8>, VaultError> {
    if vault.slots.len() > u8::MAX as usize {
        return Err(VaultError::InvalidLength);
    }
    if vault.records.len() > u16::MAX as usize {
        return Err(VaultError::InvalidLength);
    }

    let header_bytes = serialize_header(&vault.header);
    let mut out = alloc::vec::Vec::new();
    out.extend_from_slice(&header_bytes);

    let slot_count = vault.slots.len() as u8;
    out.push(slot_count);
    for slot in &vault.slots {
        let slot_bytes = serialize_slot_entry(slot)?;
        out.extend_from_slice(&slot_bytes);
    }

    let record_count = (vault.records.len() as u16).to_be_bytes();
    out.extend_from_slice(&record_count);
    for record in &vault.records {
        let record_bytes = serialize_record(record)?;
        out.extend_from_slice(&record_bytes);
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vault_header_equality() {
        let header1 = VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: 1,
        };
        let header2 = VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: 1,
        };
        assert_eq!(header1, header2, "同一パラメータのVaultHeader比較に成功。");
    }

    #[test]
    fn test_vault_error_equality() {
        let err1 = VaultError::UnexpectedEof;
        let err2 = VaultError::UnexpectedEof;
        let err3 = VaultError::InvalidMagic;
        assert_eq!(err1, err2, "同一のVaultErrorバリアント比較に成功。");
        assert_ne!(err1, err3, "異なるVaultErrorバリアント比較に成功。");

        let parse_err: TlvParseError = VaultError::InvalidLength;
        assert_eq!(
            parse_err,
            VaultError::InvalidLength,
            "TlvParseError型エイリアスとの比較に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_kek_slot_entry_equality() {
        let entry1 = KekSlotEntry {
            slot_id: 0,
            kdf_kind: 1,
            wrapped_dek_len: 4,
            wrapped_dek: alloc::vec![0x01, 0x02, 0x03, 0x04],
        };
        let entry2 = KekSlotEntry {
            slot_id: 0,
            kdf_kind: 1,
            wrapped_dek_len: 4,
            wrapped_dek: alloc::vec![0x01, 0x02, 0x03, 0x04],
        };
        assert_eq!(entry1, entry2, "同一パラメータのKekSlotEntry比較に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_tlv_record_equality() {
        let payload1 = TlvPayload::new(alloc::vec![0x01, 0x02, 0x03], [0xaa; AUTH_TAG_LEN]);
        let payload2 = TlvPayload::new(alloc::vec![0x01, 0x02, 0x03], [0xaa; AUTH_TAG_LEN]);
        let known1 = TlvRecord::Known {
            tag: 1,
            payload: payload1,
        };
        let known2 = TlvRecord::Known {
            tag: 1,
            payload: payload2,
        };
        assert_eq!(
            known1, known2,
            "同一パラメータのTlvRecord::Known比較に成功。"
        );
        assert_eq!(known1.tag(), 1, "TlvRecord::Knownからのtag取得に成功。");

        let unknown1 = TlvRecord::UnknownTag {
            tag: 99,
            raw_bytes: alloc::vec![0xde, 0xad, 0xbe, 0xef],
        };
        let unknown2 = TlvRecord::UnknownTag {
            tag: 99,
            raw_bytes: alloc::vec![0xde, 0xad, 0xbe, 0xef],
        };
        assert_eq!(
            unknown1, unknown2,
            "同一パラメータのTlvRecord::UnknownTag比較に成功。"
        );
        assert_eq!(
            unknown1.tag(),
            99,
            "TlvRecord::UnknownTagからのtag取得に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_vault_equality() {
        let header = VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: 1,
        };
        let slot = KekSlotEntry {
            slot_id: 0,
            kdf_kind: 1,
            wrapped_dek_len: 4,
            wrapped_dek: alloc::vec![0x10, 0x20, 0x30, 0x40],
        };
        let payload = TlvPayload::new(alloc::vec![0x01, 0x02], [0xbb; AUTH_TAG_LEN]);
        let record = TlvRecord::Known { tag: 1, payload };
        let vault1 = Vault::new(
            header,
            alloc::vec![slot.clone()],
            alloc::vec![record.clone()],
        );
        let vault2 = Vault::new(header, alloc::vec![slot], alloc::vec![record]);
        assert_eq!(vault1, vault2, "同一パラメータのVault比較に成功。");
    }

    #[test]
    fn test_deserialize_header_success() {
        let input = [b'F', b'V', b'A', b'U', 1, 2, 0xaa, 0xbb];
        let result = deserialize_header(&input);
        assert!(
            result.is_ok(),
            "正常なヘッダーバイト列のデシリアライズに成功。"
        );
        let (header, rest) = result.unwrap();
        assert_eq!(
            header,
            VaultHeader {
                magic: VAULT_MAGIC,
                version: 1,
                suite_id: 2,
            },
            "デシリアライズされたVaultHeaderの検証に成功。"
        );
        assert_eq!(rest, &[0xaa, 0xbb], "残余スライスの検証に成功。");
    }

    #[test]
    fn test_deserialize_header_unexpected_eof() {
        let input = [b'F', b'V', b'A', b'U', 1];
        let result = deserialize_header(&input);
        assert_eq!(
            result,
            Err(VaultError::UnexpectedEof),
            "データ長不足時のUnexpectedEof返却検証に成功。"
        );
    }

    #[test]
    fn test_deserialize_header_invalid_magic() {
        let input = [b'W', b'R', b'N', b'G', 1, 2];
        let result = deserialize_header(&input);
        assert_eq!(
            result,
            Err(VaultError::InvalidMagic),
            "不正マジックバイト時のInvalidMagic返却検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_record_known_success() {
        let mut input = alloc::vec![TAG_ENTRY, 19];
        input.extend_from_slice(&[0x01, 0x02, 0x03]);
        input.extend_from_slice(&[0xaa; AUTH_TAG_LEN]);
        input.extend_from_slice(&[0xee, 0xff]);

        let result = deserialize_record(&input);
        assert!(
            result.is_ok(),
            "既知タグレコードの正常系デシリアライズに成功。"
        );
        let (record, rest) = result.unwrap();
        assert_eq!(
            record,
            TlvRecord::Known {
                tag: TAG_ENTRY,
                payload: TlvPayload::new(alloc::vec![0x01, 0x02, 0x03], [0xaa; AUTH_TAG_LEN]),
            },
            "デシリアライズされた既知レコード内容の検証に成功。"
        );
        assert_eq!(
            rest,
            &[0xee, 0xff],
            "レコードパース後の残余スライス検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_record_unknown_success() {
        let input = [99, 4, 0xde, 0xad, 0xbe, 0xef, 0x12, 0x34];
        let result = deserialize_record(&input);
        assert!(
            result.is_ok(),
            "未知タグレコードの無害な読み飛ばしデシリアライズに成功。"
        );
        let (record, rest) = result.unwrap();
        assert_eq!(
            record,
            TlvRecord::UnknownTag {
                tag: 99,
                raw_bytes: alloc::vec![0xde, 0xad, 0xbe, 0xef],
            },
            "デシリアライズされた未知タグレコード内容の検証に成功。"
        );
        assert_eq!(
            rest,
            &[0x12, 0x34],
            "未知タグパース後の残余スライス検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_record_unexpected_eof() {
        let short_header = [TAG_ENTRY];
        assert_eq!(
            deserialize_record(&short_header),
            Err(VaultError::UnexpectedEof),
            "ヘッダー長不足時のUnexpectedEof検証に成功。"
        );

        let short_payload = [TAG_ENTRY, 10, 0x01, 0x02];
        assert_eq!(
            deserialize_record(&short_payload),
            Err(VaultError::UnexpectedEof),
            "宣言長不足時のUnexpectedEof検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_record_invalid_length() {
        let input = [TAG_ENTRY, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
        assert_eq!(
            deserialize_record(&input),
            Err(VaultError::InvalidLength),
            "既知タグで認証タグ長未満時のInvalidLength検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_slot_entry_success() {
        let input = [1, 2, 0x00, 0x04, 0xaa, 0xbb, 0xcc, 0xdd, 0xff];
        let result = deserialize_slot_entry(&input);
        assert!(
            result.is_ok(),
            "KEKスロットエントリの正常系デシリアライズに成功。"
        );
        let (entry, rest) = result.unwrap();
        assert_eq!(
            entry,
            KekSlotEntry {
                slot_id: 1,
                kdf_kind: 2,
                wrapped_dek_len: 4,
                wrapped_dek: alloc::vec![0xaa, 0xbb, 0xcc, 0xdd],
            },
            "デシリアライズされたKekSlotEntry内容の検証に成功。"
        );
        assert_eq!(rest, &[0xff], "スロットパース後の残余スライス検証に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_slot_entry_unexpected_eof() {
        let short_header = [1, 2, 0x01];
        assert_eq!(
            deserialize_slot_entry(&short_header),
            Err(VaultError::UnexpectedEof),
            "ヘッダー長不足時のUnexpectedEof検証に成功。"
        );

        let short_payload = [1, 2, 0x00, 0x04, 0xaa, 0xbb];
        assert_eq!(
            deserialize_slot_entry(&short_payload),
            Err(VaultError::UnexpectedEof),
            "ペイロード長不足時のUnexpectedEof検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_vault_success() {
        let mut input = alloc::vec![b'F', b'V', b'A', b'U', 1, 2];
        // 1スロット
        input.push(1);
        input.extend_from_slice(&[0, 1, 0x00, 0x04, 0x11, 0x22, 0x33, 0x44]);
        // 2レコード
        input.extend_from_slice(&[0x00, 0x02]);
        // レコード1: 既知タグ
        input.extend_from_slice(&[TAG_ENTRY, 19]);
        input.extend_from_slice(&[0x01, 0x02, 0x03]);
        input.extend_from_slice(&[0xaa; AUTH_TAG_LEN]);
        // レコード2: 未知タグ
        input.extend_from_slice(&[99, 4, 0xde, 0xad, 0xbe, 0xef]);
        // 残余バイト
        input.extend_from_slice(&[0x99, 0x88]);

        let result = deserialize(&input);
        assert!(result.is_ok(), "Vault全体の正常系デシリアライズに成功。");
        let (vault, rest) = result.unwrap();
        assert_eq!(
            vault.header,
            VaultHeader {
                magic: VAULT_MAGIC,
                version: 1,
                suite_id: 2,
            },
            "デシリアライズされたVaultHeaderの検証に成功。"
        );
        assert_eq!(
            vault.slots,
            alloc::vec![KekSlotEntry {
                slot_id: 0,
                kdf_kind: 1,
                wrapped_dek_len: 4,
                wrapped_dek: alloc::vec![0x11, 0x22, 0x33, 0x44],
            }],
            "デシリアライズされたスロットテーブルの検証に成功。"
        );
        assert_eq!(
            vault.records,
            alloc::vec![
                TlvRecord::Known {
                    tag: TAG_ENTRY,
                    payload: TlvPayload::new(alloc::vec![0x01, 0x02, 0x03], [0xaa; AUTH_TAG_LEN]),
                },
                TlvRecord::UnknownTag {
                    tag: 99,
                    raw_bytes: alloc::vec![0xde, 0xad, 0xbe, 0xef],
                },
            ],
            "デシリアライズされたレコード群の検証に成功。"
        );
        assert_eq!(
            rest,
            &[0x99, 0x88],
            "Vault全体のパース後残余スライス検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_vault_empty_slots_and_records() {
        let input = [b'F', b'V', b'A', b'U', 1, 1, 0, 0x00, 0x00];
        let result = deserialize(&input);
        assert!(
            result.is_ok(),
            "空スロットおよび空レコードのVaultデシリアライズに成功。"
        );
        let (vault, rest) = result.unwrap();
        assert!(
            vault.slots.is_empty(),
            "スロットテーブルが空であることの検証に成功。"
        );
        assert!(
            vault.records.is_empty(),
            "レコード群が空であることの検証に成功。"
        );
        assert!(rest.is_empty(), "残余スライスが空であることの検証に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_vault_unexpected_eof() {
        // ヘッダー不足
        assert_eq!(
            deserialize(b"FVA"),
            Err(VaultError::UnexpectedEof),
            "Vaultヘッダー長不足時のUnexpectedEof検証に成功。"
        );

        // slot_count不足
        let header_only = [b'F', b'V', b'A', b'U', 1, 1];
        assert_eq!(
            deserialize(&header_only),
            Err(VaultError::UnexpectedEof),
            "slot_count不足時のUnexpectedEof検証に成功。"
        );

        // スロットデータ不足
        let slot_missing = [b'F', b'V', b'A', b'U', 1, 1, 1, 0, 1];
        assert_eq!(
            deserialize(&slot_missing),
            Err(VaultError::UnexpectedEof),
            "スロットデータ不足時のUnexpectedEof検証に成功。"
        );

        // record_count不足
        let record_count_missing = [b'F', b'V', b'A', b'U', 1, 1, 0, 0x00];
        assert_eq!(
            deserialize(&record_count_missing),
            Err(VaultError::UnexpectedEof),
            "record_count不足時のUnexpectedEof検証に成功。"
        );

        // レコードデータ不足
        let record_missing = [b'F', b'V', b'A', b'U', 1, 1, 0, 0x00, 0x01, TAG_ENTRY, 10];
        assert_eq!(
            deserialize(&record_missing),
            Err(VaultError::UnexpectedEof),
            "レコードデータ不足時のUnexpectedEof検証に成功。"
        );

        // slot_count事前境界チェック(Allocation DoS防止)
        let slot_dos_attack = [b'F', b'V', b'A', b'U', 1, 1, 255, 0, 1];
        assert_eq!(
            deserialize(&slot_dos_attack),
            Err(VaultError::UnexpectedEof),
            "過大slot_countによる事前境界チェック(Allocation DoS防止)の検証に成功。"
        );

        // record_count事前境界チェック(Allocation DoS防止)
        let record_dos_attack = [b'F', b'V', b'A', b'U', 1, 1, 0, 0xff, 0xff, 1, 2];
        assert_eq!(
            deserialize(&record_dos_attack),
            Err(VaultError::UnexpectedEof),
            "過大record_countによる事前境界チェック(Allocation DoS防止)の検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_vault_invalid_magic() {
        let input = [b'X', b'X', b'X', b'X', 1, 1, 0, 0x00, 0x00];
        assert_eq!(
            deserialize(&input),
            Err(VaultError::InvalidMagic),
            "不正マジックバイト時のInvalidMagic検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_deserialize_vault_record_error() {
        let input = [
            b'F', b'V', b'A', b'U', 1, 1, 0, 0x00, 0x01, TAG_ENTRY, 10, 0, 1, 2, 3, 4, 5, 6, 7, 8,
            9,
        ];
        assert_eq!(
            deserialize(&input),
            Err(VaultError::InvalidLength),
            "不正レコード含有時のエラー伝播検証に成功。"
        );
    }

    #[test]
    fn test_serialize_header_and_roundtrip() {
        let header = VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: 3,
        };
        let bytes = serialize_header(&header);
        assert_eq!(
            bytes,
            [b'F', b'V', b'A', b'U', 1, 3],
            "VaultHeaderのシリアライズ結果検証に成功。"
        );

        let (deserialized, rest) = deserialize_header(&bytes).expect("デシリアライズに成功。");
        assert_eq!(
            deserialized, header,
            "VaultHeaderのシリアライズ・デシリアライズ往復に成功。"
        );
        assert!(rest.is_empty(), "残余スライスが空であることの検証に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_slot_entry_and_roundtrip() {
        let entry = KekSlotEntry {
            slot_id: 2,
            kdf_kind: 1,
            wrapped_dek_len: 3,
            wrapped_dek: alloc::vec![0xaa, 0xbb, 0xcc],
        };
        let bytes = serialize_slot_entry(&entry).expect("シリアライズに成功。");
        assert_eq!(
            bytes,
            [2, 1, 0x00, 0x03, 0xaa, 0xbb, 0xcc],
            "KekSlotEntryのシリアライズ結果検証に成功。"
        );

        let (deserialized, rest) = deserialize_slot_entry(&bytes).expect("デシリアライズに成功。");
        assert_eq!(
            deserialized, entry,
            "KekSlotEntryのシリアライズ・デシリアライズ往復に成功。"
        );
        assert!(rest.is_empty(), "残余スライスが空であることの検証に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_slot_entry_mismatched_length() {
        let entry = KekSlotEntry {
            slot_id: 1,
            kdf_kind: 1,
            wrapped_dek_len: 4,
            wrapped_dek: alloc::vec![0x01, 0x02],
        };
        assert_eq!(
            serialize_slot_entry(&entry),
            Err(VaultError::InvalidLength),
            "実体長と宣言長の不一致時におけるInvalidLength返却検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_kek_slot_entry_new() {
        let entry = KekSlotEntry::new(0, 1, alloc::vec![0x10, 0x20])
            .expect("正常なパラメータによるKekSlotEntry生成に成功。");
        assert_eq!(entry.slot_id, 0);
        assert_eq!(entry.kdf_kind, 1);
        assert_eq!(entry.wrapped_dek_len, 2);
        assert_eq!(entry.wrapped_dek, alloc::vec![0x10, 0x20]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_record_known_and_roundtrip() {
        let record = TlvRecord::Known {
            tag: TAG_ENTRY,
            payload: TlvPayload::new(alloc::vec![0x10, 0x20, 0x30], [0xcc; AUTH_TAG_LEN]),
        };
        let bytes = serialize_record(&record).expect("既知レコードのシリアライズに成功。");
        assert_eq!(bytes[0], TAG_ENTRY, "シリアライズ後タグの一致確認に成功。");
        assert_eq!(
            bytes[1],
            (3 + AUTH_TAG_LEN) as u8,
            "シリアライズ後データ長の一致確認に成功。"
        );

        let (deserialized, rest) = deserialize_record(&bytes).expect("デシリアライズに成功。");
        assert_eq!(
            deserialized, record,
            "既知TlvRecordのシリアライズ・デシリアライズ往復に成功。"
        );
        assert!(rest.is_empty(), "残余スライスが空であることの検証に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_record_unknown_and_roundtrip() {
        let record = TlvRecord::UnknownTag {
            tag: 88,
            raw_bytes: alloc::vec![0x01, 0x02, 0x03, 0x04],
        };
        let bytes = serialize_record(&record).expect("未知タグレコードのシリアライズに成功。");
        assert_eq!(bytes[0], 88, "未知タグの一致確認に成功。");
        assert_eq!(bytes[1], 4, "未知データ長の一致確認に成功。");

        let (deserialized, rest) = deserialize_record(&bytes).expect("デシリアライズに成功。");
        assert_eq!(
            deserialized, record,
            "未知TlvRecordのシリアライズ・デシリアライズ往復に成功。"
        );
        assert!(rest.is_empty(), "残余スライスが空であることの検証に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_record_overflow() {
        let large_ciphertext = alloc::vec![0u8; 250];
        let record = TlvRecord::Known {
            tag: TAG_ENTRY,
            payload: TlvPayload::new(large_ciphertext, [0x00; AUTH_TAG_LEN]),
        };
        let res = serialize_record(&record);
        assert_eq!(
            res,
            Err(VaultError::InvalidLength),
            "既知レコード長が255超過時のInvalidLength返却検証に成功。"
        );

        let large_unknown = alloc::vec![0u8; 256];
        let record_unknown = TlvRecord::UnknownTag {
            tag: 50,
            raw_bytes: large_unknown,
        };
        let res_unknown = serialize_record(&record_unknown);
        assert_eq!(
            res_unknown,
            Err(VaultError::InvalidLength),
            "未知レコード長が255超過時のInvalidLength返却検証に成功。"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_vault_and_roundtrip() {
        let header = VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: 2,
        };
        let slot = KekSlotEntry {
            slot_id: 0,
            kdf_kind: 1,
            wrapped_dek_len: 4,
            wrapped_dek: alloc::vec![0x10, 0x20, 0x30, 0x40],
        };
        let record1 = TlvRecord::Known {
            tag: TAG_ENTRY,
            payload: TlvPayload::new(alloc::vec![0x01, 0x02, 0x03], [0xaa; AUTH_TAG_LEN]),
        };
        let record2 = TlvRecord::UnknownTag {
            tag: 99,
            raw_bytes: alloc::vec![0xde, 0xad, 0xbe, 0xef],
        };
        let vault = Vault::new(header, alloc::vec![slot], alloc::vec![record1, record2]);

        let bytes = serialize(&vault).expect("Vaultシリアライズに成功。");
        let (deserialized, rest) = deserialize(&bytes).expect("Vaultデシリアライズに成功。");
        assert_eq!(
            deserialized, vault,
            "Vault全体のシリアライズ・デシリアライズ往復に成功。"
        );
        assert!(rest.is_empty(), "残余スライスが空であることの検証に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_vault_empty() {
        let header = VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: 1,
        };
        let vault = Vault::new(header, alloc::vec::Vec::new(), alloc::vec::Vec::new());
        let bytes = serialize(&vault).expect("空Vaultシリアライズに成功。");
        let (deserialized, rest) = deserialize(&bytes).expect("空Vaultデシリアライズに成功。");
        assert_eq!(
            deserialized, vault,
            "空Vaultのシリアライズ・デシリアライズ往復に成功。"
        );
        assert!(rest.is_empty(), "残余スライスが空であることの検証に成功。");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_serialize_vault_slot_overflow() {
        let header = VaultHeader {
            magic: VAULT_MAGIC,
            version: 1,
            suite_id: 1,
        };
        let slot = KekSlotEntry {
            slot_id: 0,
            kdf_kind: 1,
            wrapped_dek_len: 0,
            wrapped_dek: alloc::vec::Vec::new(),
        };
        let slots = alloc::vec![slot; 256];
        let vault = Vault::new(header, slots, alloc::vec::Vec::new());
        let res = serialize(&vault);
        assert_eq!(
            res,
            Err(VaultError::InvalidLength),
            "スロット数が255超過時のInvalidLength返却検証に成功。"
        );
    }
}
