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
    /// AEAD暗号化処理に失敗。
    AeadEncryptionFailed,
    /// 鍵導出処理(Argon2id, HKDF等)に失敗。
    KeyDerivationFailed,
    /// 鍵のサイズが要求長と一致しない。
    InvalidKeySize,
    /// ノンス(初期化ベクトル)のサイズが不正。
    InvalidNonceSize,
    /// 認証タグのサイズが不正。
    InvalidTagSize,
    /// 入力スライス長が不正または許容上限を超過。
    InvalidSliceLength,
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
    /// 現在のVault状態に対して不正な状態遷移または操作が要求された。
    InvalidState,
    /// 外部公開境界における一様認証失敗例外(オラクル排除・情報流非干渉性保証用)。
    AuthenticationFailed,
    /// 世代カウンター(`epoch_id`)の巻き戻し・ロールバック攻撃を検知した例外。
    RollbackDetected,
}

impl VaultError {
    /// 外部公開API境界におけるオラクル排除のため、内部詳細エラーを
    /// 単一の [`VaultError::AuthenticationFailed`] へ一様マスキングする。
    ///
    /// FSM の公開状態契約違反を表す [`VaultError::InvalidState`] および、
    /// 世代巻き戻し検証結果を表す [`VaultError::RollbackDetected`] を除き、
    /// スロット不在 ([`VaultError::SlotNotFound`])、MAC 不一致や鍵長不正 ([`VaultError::Crypto`])、
    /// スロット形式・重複・長さ異常 ([`VaultError::Parse`])、システム例外 ([`VaultError::System`]) 等の
    /// 内部詳細エラーをすべて [`VaultError::AuthenticationFailed`] へ畳み込む。
    #[inline]
    #[must_use]
    pub const fn mask_auth_error(self) -> Self {
        match self {
            Self::InvalidState => Self::InvalidState,
            Self::RollbackDetected => Self::RollbackDetected,
            Self::Parse(_)
            | Self::Crypto(_)
            | Self::System(_)
            | Self::SlotNotFound
            | Self::AuthenticationFailed => Self::AuthenticationFailed,
        }
    }
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
            Self::AeadEncryptionFailed => write!(f, "AEAD暗号化処理に失敗しました。"),
            Self::KeyDerivationFailed => write!(f, "鍵導出処理に失敗しました。"),
            Self::InvalidKeySize => write!(f, "不正な鍵サイズです。"),
            Self::InvalidNonceSize => write!(f, "不正なノンスサイズです。"),
            Self::InvalidTagSize => write!(f, "不正な認証タグサイズです。"),
            Self::InvalidSliceLength => {
                write!(f, "入力スライス長が不正または許容上限を超過しています。")
            }
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
            Self::InvalidState => write!(f, "現在の状態では実行できない不正な状態遷移です。"),
            Self::AuthenticationFailed => write!(f, "認証に失敗しました。"),
            Self::RollbackDetected => {
                write!(f, "世代カウンターの巻き戻し(ロールバック)を検知しました。")
            }
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
        let err4 = CryptoError::AeadEncryptionFailed;
        let err5 = CryptoError::InvalidSliceLength;
        assert_eq!(err1, err2, "同一のCryptoErrorバリアント比較に成功。");
        assert_ne!(err1, err3, "異なるCryptoErrorバリアント比較に成功。");
        assert_ne!(err1, err4, "AeadEncryptionFailedとの比較に成功。");
        assert_ne!(err1, err5, "InvalidSliceLengthとの比較に成功。");
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

        let encrypt_err_msg = format!("{}", VaultError::Crypto(CryptoError::AeadEncryptionFailed));
        assert!(
            encrypt_err_msg.contains("AEAD暗号化処理に失敗しました。"),
            "AeadEncryptionFailedのDisplay出力に成功。"
        );

        let slice_err_msg = format!("{}", VaultError::Crypto(CryptoError::InvalidSliceLength));
        assert!(
            slice_err_msg.contains("入力スライス長が不正または許容上限を超過しています。"),
            "InvalidSliceLengthのDisplay出力に成功。"
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

        let invalid_state_msg = format!("{}", VaultError::InvalidState);
        assert_eq!(
            invalid_state_msg, "現在の状態では実行できない不正な状態遷移です。",
            "VaultError::InvalidStateのDisplay出力に成功。"
        );

        let auth_msg = format!("{}", VaultError::AuthenticationFailed);
        assert_eq!(
            auth_msg, "認証に失敗しました。",
            "VaultError::AuthenticationFailedのDisplay出力に成功。"
        );

        let rollback_msg = format!("{}", VaultError::RollbackDetected);
        assert_eq!(
            rollback_msg, "世代カウンターの巻き戻し(ロールバック)を検知しました。",
            "VaultError::RollbackDetectedのDisplay出力に成功。"
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

    #[test]
    fn test_vault_error_mask_auth_error() {
        let masked_variants = [
            VaultError::SlotNotFound,
            VaultError::AuthenticationFailed,
            VaultError::Parse(TlvParseError::UnexpectedEof),
            VaultError::Parse(TlvParseError::InvalidFormat),
            VaultError::Parse(TlvParseError::InvalidLength),
            VaultError::Parse(TlvParseError::UnsupportedSuite),
            VaultError::Crypto(CryptoError::AeadDecryptionFailed),
            VaultError::Crypto(CryptoError::KeyDerivationFailed),
            VaultError::Crypto(CryptoError::InvalidKeySize),
            VaultError::Crypto(CryptoError::InvalidParameter),
            VaultError::Crypto(CryptoError::InvalidSliceLength),
            VaultError::System(SystemError::MemoryLockFailed),
            VaultError::System(SystemError::EntropySourceFailed),
        ];

        for err in masked_variants {
            assert_eq!(
                err.mask_auth_error(),
                VaultError::AuthenticationFailed,
                "内部詳細エラーがAuthenticationFailedへ一様マスキングされることを確認。"
            );
        }

        assert_eq!(
            VaultError::InvalidState.mask_auth_error(),
            VaultError::InvalidState,
            "公開状態契約違反InvalidStateが保持されることを確認。"
        );
        assert_eq!(
            VaultError::RollbackDetected.mask_auth_error(),
            VaultError::RollbackDetected,
            "ロールバック検知RollbackDetectedが保持されることを確認。"
        );
    }
}
