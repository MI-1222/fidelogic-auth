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
}
