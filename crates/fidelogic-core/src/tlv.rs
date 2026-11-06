//! # 最小限のゼロコピーTLVパーサー
//!
//! Charon / Aeneas 形式検証ターゲット用の純粋関数型パースロジック。

#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct TlvHeader {
    pub tag: u8,
    pub length: u8,
}

/// 2バイトのヘッダー [Tag (1B), Length (1B)] を安全に取得する。
#[must_use]
pub fn parse_tlv_header(bytes: &[u8]) -> Option<TlvHeader> {
    if bytes.len() < 2 {
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
        let required_len = 2usize + (header.length as usize);
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

/// KEKスロット定義テーブルのエントリを表す固定長レコード。
///
/// スロットID, KDF種別, ラップ済みDEKのバイト長を保持する。
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct KekSlotEntry {
    /// スロット識別子。
    pub slot_id: u8,
    /// 鍵導出関数(KDF)の種別。
    pub kdf_kind: u8,
    /// ラップ済みDEKのバイト長。
    pub wrapped_dek_len: u16,
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

    #[test]
    fn test_kek_slot_entry_equality() {
        let entry1 = KekSlotEntry {
            slot_id: 0,
            kdf_kind: 1,
            wrapped_dek_len: 64,
        };
        let entry2 = KekSlotEntry {
            slot_id: 0,
            kdf_kind: 1,
            wrapped_dek_len: 64,
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
            wrapped_dek_len: 64,
        };
        let payload = TlvPayload::new(alloc::vec![0x01, 0x02], [0xbb; AUTH_TAG_LEN]);
        let record = TlvRecord::Known { tag: 1, payload };
        let vault1 = Vault::new(header, alloc::vec![slot], alloc::vec![record.clone()]);
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
}
