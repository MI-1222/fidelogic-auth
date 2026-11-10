//! # エラー型定義モジュール。
//!
//! Fidelogicにおける階層的エラーハンドリング体系を提供する。
//! 形式検証と結合した [`TlvParseError`] を完全温存し、
//! 暗号処理例外 [`CryptoError`]、システム例外 [`SystemError`]、
//! およびそれらを統合する包括的ドメインエラー [`VaultError`] を定義する。

/// TLVおよびVaultパース処理で発生するフォーマット例外を表す列挙型。
///
/// 形式検証(Rocq証明資産)と1対1で対応するバリアントを温存し、
/// パニックを完全に排除して境界外アクセスや不正フォーマットを純粋な値として通知する。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TlvParseError {
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

/// 暗号処理(鍵導出・暗号化・復号・パラメータ検証)で発生する例外を表す列挙型。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CryptoError {
    /// AEAD復号または認証タグの照合に失敗。
    AeadDecryptionFailed,
    /// 鍵導出処理(Argon2id, HKDF等)に失敗。
    KeyDerivationFailed,
    /// 鍵のサイズが要求長と一致しない。
    InvalidKeySize,
    /// ノンス(初期化ベクトル)のサイズが不正。
    InvalidNonceSize,
    /// 認証タグのサイズが不正。
    InvalidTagSize,
    /// 暗号パラメータ(反復回数、メモリサイズ等)が不正。
    InvalidParameter,
}

/// OSシステムコールまたはランタイム環境に起因する例外を表す列挙型。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SystemError {
    /// メモリロック(mlock, madvise等)の要求に失敗。
    MemoryLockFailed,
    /// 暗号論的エントロピー源(乱数生成器)の初期化または取得に失敗。
    EntropySourceFailed,
}

/// Fidelogic Vaultにおける統括ドメインエラーを表す列挙型。
///
/// TLVパース例外、暗号処理例外、システム例外を階層的に内包し、
/// 外部境界向けの一様マスキングバリアントを提供する。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VaultError {
    /// TLVパースおよびフォーマット検証に起因する例外。
    Parse(TlvParseError),
    /// 暗号処理に起因する例外。
    Crypto(CryptoError),
    /// OSシステムコールおよび環境に起因する例外。
    System(SystemError),
    /// 指定された識別子のKEKスロットが存在しない。
    SlotNotFound,
    /// 外部公開境界における一様認証失敗例外(オラクル排除・情報流非干渉性保証用)。
    AuthenticationFailed,
}

impl From<TlvParseError> for VaultError {
    #[inline]
    fn from(err: TlvParseError) -> Self {
        Self::Parse(err)
    }
}

impl From<CryptoError> for VaultError {
    #[inline]
    fn from(err: CryptoError) -> Self {
        Self::Crypto(err)
    }
}

impl From<SystemError> for VaultError {
    #[inline]
    fn from(err: SystemError) -> Self {
        Self::System(err)
    }
}

impl core::fmt::Display for TlvParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnexpectedEof => write!(f, "入力バイト列の長さが不足しています。"),
            Self::InvalidMagic => write!(f, "マジックバイトが一致しません。"),
            Self::UnsupportedVersion => write!(f, "非対応のフォーマットバージョンです。"),
            Self::UnsupportedSuite => write!(f, "非対応の暗号スイートです。"),
            Self::InvalidLength => write!(f, "データ長が不正です。"),
            Self::InvalidFormat => write!(f, "フォーマットが不正です。"),
        }
    }
}

impl core::fmt::Display for CryptoError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::AeadDecryptionFailed => write!(f, "AEAD復号または認証タグの照合に失敗しました。"),
            Self::KeyDerivationFailed => write!(f, "鍵導出処理に失敗しました。"),
            Self::InvalidKeySize => write!(f, "不正な鍵サイズです。"),
            Self::InvalidNonceSize => write!(f, "不正なノンスサイズです。"),
            Self::InvalidTagSize => write!(f, "不正な認証タグサイズです。"),
            Self::InvalidParameter => write!(f, "不正な暗号パラメータです。"),
        }
    }
}

impl core::fmt::Display for SystemError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::MemoryLockFailed => write!(f, "メモリロックの実行に失敗しました。"),
            Self::EntropySourceFailed => write!(f, "エントロピー源の取得に失敗しました。"),
        }
    }
}

impl core::fmt::Display for VaultError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Parse(err) => write!(f, "パースエラー: {err}"),
            Self::Crypto(err) => write!(f, "暗号エラー: {err}"),
            Self::System(err) => write!(f, "システムエラー: {err}"),
            Self::SlotNotFound => write!(f, "指定されたスロットが存在しません。"),
            Self::AuthenticationFailed => write!(f, "認証に失敗しました。"),
        }
    }
}

impl core::error::Error for TlvParseError {}
impl core::error::Error for CryptoError {}
impl core::error::Error for SystemError {}

impl core::error::Error for VaultError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::Parse(err) => Some(err),
            Self::Crypto(err) => Some(err),
            Self::System(err) => Some(err),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tlv_parse_error_equality() {
        let err1 = TlvParseError::UnexpectedEof;
        let err2 = TlvParseError::UnexpectedEof;
        let err3 = TlvParseError::InvalidMagic;
        assert_eq!(err1, err2, "同一のTlvParseErrorバリアント比較に成功。");
        assert_ne!(err1, err3, "異なるTlvParseErrorバリアント比較に成功。");
    }

    #[test]
    fn test_crypto_error_equality() {
        let err1 = CryptoError::AeadDecryptionFailed;
        let err2 = CryptoError::AeadDecryptionFailed;
        let err3 = CryptoError::KeyDerivationFailed;
        assert_eq!(err1, err2, "同一のCryptoErrorバリアント比較に成功。");
        assert_ne!(err1, err3, "異なるCryptoErrorバリアント比較に成功。");
    }

    #[test]
    fn test_system_error_equality() {
        let err1 = SystemError::MemoryLockFailed;
        let err2 = SystemError::MemoryLockFailed;
        let err3 = SystemError::EntropySourceFailed;
        assert_eq!(err1, err2, "同一のSystemErrorバリアント比較に成功。");
        assert_ne!(err1, err3, "異なるSystemErrorバリアント比較に成功。");
    }

    #[test]
    fn test_vault_error_from_conversions() {
        let parse_err = TlvParseError::InvalidLength;
        let vault_err_parse: VaultError = parse_err.into();
        assert_eq!(
            vault_err_parse,
            VaultError::Parse(TlvParseError::InvalidLength),
            "TlvParseErrorからVaultErrorへのFrom変換に成功。"
        );

        let crypto_err = CryptoError::AeadDecryptionFailed;
        let vault_err_crypto: VaultError = crypto_err.into();
        assert_eq!(
            vault_err_crypto,
            VaultError::Crypto(CryptoError::AeadDecryptionFailed),
            "CryptoErrorからVaultErrorへのFrom変換に成功。"
        );

        let system_err = SystemError::MemoryLockFailed;
        let vault_err_system: VaultError = system_err.into();
        assert_eq!(
            vault_err_system,
            VaultError::System(SystemError::MemoryLockFailed),
            "SystemErrorからVaultErrorへのFrom変換に成功。"
        );
    }

    #[test]
    fn test_vault_error_display() {
        use alloc::format;

        let parse_msg = format!("{}", VaultError::Parse(TlvParseError::UnexpectedEof));
        assert!(
            parse_msg.contains("入力バイト列の長さが不足しています。"),
            "VaultError::ParseのDisplay出力に成功。"
        );

        let crypto_msg = format!("{}", VaultError::Crypto(CryptoError::InvalidKeySize));
        assert!(
            crypto_msg.contains("不正な鍵サイズです。"),
            "VaultError::CryptoのDisplay出力に成功。"
        );

        let system_msg = format!("{}", VaultError::System(SystemError::MemoryLockFailed));
        assert!(
            system_msg.contains("メモリロックの実行に失敗しました。"),
            "VaultError::SystemのDisplay出力に成功。"
        );

        let slot_msg = format!("{}", VaultError::SlotNotFound);
        assert_eq!(
            slot_msg, "指定されたスロットが存在しません。",
            "VaultError::SlotNotFoundのDisplay出力に成功。"
        );

        let auth_msg = format!("{}", VaultError::AuthenticationFailed);
        assert_eq!(
            auth_msg, "認証に失敗しました。",
            "VaultError::AuthenticationFailedのDisplay出力に成功。"
        );
    }

    #[test]
    fn test_vault_error_source() {
        use core::error::Error;

        let vault_parse = VaultError::Parse(TlvParseError::InvalidMagic);
        assert!(
            vault_parse.source().is_some(),
            "VaultError::Parseのsource取得に成功。"
        );

        let vault_auth = VaultError::AuthenticationFailed;
        assert!(
            vault_auth.source().is_none(),
            "VaultError::AuthenticationFailedのsourceがNoneであることに成功。"
        );
    }
}
