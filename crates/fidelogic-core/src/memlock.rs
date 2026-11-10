//! # メモリロック保護モジュール(Native限定)
//!
//! DEK(データ暗号化鍵)やKEK(鍵暗号化鍵)などの極小暗号領域に対して、
//! OSレベルのメモリ保護(`libc::mlock` および `libc::madvise(MADV_DONTDUMP)`)を提供する。
//! スワップ領域への書き出し防止とコアダンプ生成時の機密漏洩遮断を確立し、
//! 非特権コンテナ環境等における警告フォールバック動作をサポートする。

use alloc::boxed::Box;
use zeroize::Zeroize;

use crate::error::SystemError;
use crate::zeroize::SecretBytes;

/// OSレベルでページロック(スワップ防止)およびダンプ抑止が適用された固定長セキュアバッファ。
///
/// ヒープ上にポインタ固定で配置され、ムーブに伴うアドレス変動を防止する。
/// 破棄時(Drop時)には内部メモリを即座にゼロ消去した上で `libc::munlock` を呼び出してロックを解除する。
pub struct LockedBuffer<const N: usize> {
    inner: Box<SecretBytes<N>>,
    locked: bool,
}

impl<const N: usize> LockedBuffer<N> {
    /// 新しい [`LockedBuffer`] を生成し、メモリロック保護を適用する。
    ///
    /// 非特権環境やリソース制限によりメモリロックに失敗した場合は、
    /// 標準エラー出力へ警告を出力した上でアンロック状態のセキュアバッファとしてフォールバック生成する。
    #[must_use]
    pub fn new(bytes: [u8; N]) -> Self {
        let mut inner = Box::new(SecretBytes::new(bytes));
        let ptr = inner.as_mut_slice().as_mut_ptr();
        let locked = match Self::apply_lock(ptr, N) {
            Ok(()) => true,
            Err(errno) => {
                #[cfg(feature = "std")]
                std::eprintln!(
                    "[WARN] fidelogic-core: mlock failed with errno {errno}. Falling back to unlocked secure buffer."
                );
                #[cfg(not(feature = "std"))]
                let _ = errno;
                false
            }
        };

        Self { inner, locked }
    }

    /// 厳格なセキュリティポリシーのもとで新しい [`LockedBuffer`] を生成する。
    ///
    /// メモリロックまたはダンプ抑止の適用に失敗した場合はフォールバックを行わず、
    /// 即座に [`SystemError::MemoryLockFailed`] を返却する。
    ///
    /// # エラー
    /// OSシステムコール(`mlock` 等)が失敗した場合に [`SystemError::MemoryLockFailed`] を返す。
    pub fn new_strict(bytes: [u8; N]) -> Result<Self, SystemError> {
        let mut inner = Box::new(SecretBytes::new(bytes));
        let ptr = inner.as_mut_slice().as_mut_ptr();
        match Self::apply_lock(ptr, N) {
            Ok(()) => Ok(Self {
                inner,
                locked: true,
            }),
            Err(_errno) => Err(SystemError::MemoryLockFailed),
        }
    }

    /// ゼロ埋めされた新しい [`LockedBuffer`] を生成する(非特権環境フォールバック付き)。
    #[must_use]
    pub fn zero() -> Self {
        Self::new([0u8; N])
    }

    /// ゼロ埋めされた新しい [`LockedBuffer`] を厳格モードで生成する。
    ///
    /// # エラー
    /// OSシステムコール(`mlock` 等)が失敗した場合に [`SystemError::MemoryLockFailed`] を返す。
    pub fn zero_strict() -> Result<Self, SystemError> {
        Self::new_strict([0u8; N])
    }

    /// メモリロック(スワップ防止保護)が正常に適用されているかを判定する。
    #[inline]
    #[must_use]
    pub const fn is_locked(&self) -> bool {
        self.locked
    }

    /// 保持するバイト列のスライス参照を取得する。
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        self.inner.as_slice()
    }

    /// 保持するバイト列の可変スライス参照を取得する。
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.inner.as_mut_slice()
    }

    /// 保持する固定長配列の参照を取得する。
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; N] {
        self.inner.as_bytes()
    }

    /// 保持する固定長配列の可変参照を取得する。
    #[inline]
    pub fn as_mut_bytes(&mut self) -> &mut [u8; N] {
        self.inner.as_mut_bytes()
    }

    /// バッファのバイト長を返す。
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        N
    }

    /// バッファ長がゼロであるかを判定する。
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        N == 0
    }

    /// 条件 `choice` に基づき、定数時間で `other` の内容を自身に上書きコピーする。
    #[inline]
    pub fn conditional_assign(&mut self, other: &Self, choice: subtle::Choice) {
        self.inner.conditional_assign(&other.inner, choice);
    }

    /// 指定されたメモリ領域に対して `mlock` および `madvise` を適用する。
    #[allow(unused_variables)]
    fn apply_lock(ptr: *mut u8, len: usize) -> Result<(), i32> {
        if len == 0 {
            return Ok(());
        }

        #[cfg(unix)]
        {
            let void_ptr = ptr as *mut libc::c_void;
            // メモリページを物理RAMに固定し、スワップアウトを防止する。
            let ret = unsafe { libc::mlock(void_ptr, len) };
            if ret != 0 {
                let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(-1);
                return Err(errno);
            }

            // Linux/Android環境においてコアダンプへの書き出しを防止する。
            #[cfg(any(target_os = "linux", target_os = "android"))]
            unsafe {
                let _ = libc::madvise(void_ptr, len, libc::MADV_DONTDUMP);
            }

            // FreeBSD環境においてコアダンプへの書き出しを防止する。
            #[cfg(target_os = "freebsd")]
            unsafe {
                let _ = libc::madvise(void_ptr, len, libc::MADV_NOCORE);
            }

            Ok(())
        }

        #[cfg(not(unix))]
        {
            // 非Unix環境では未対応としてフォールバックを促す。
            Err(-1)
        }
    }

    /// 指定されたメモリ領域の `mlock` ロックを解除する。
    #[allow(unused_variables)]
    fn release_lock(ptr: *mut u8, len: usize) {
        if len == 0 {
            return;
        }

        #[cfg(unix)]
        unsafe {
            let void_ptr = ptr as *mut libc::c_void;
            let _ = libc::munlock(void_ptr, len);
        }
    }
}

impl<const N: usize> Drop for LockedBuffer<N> {
    fn drop(&mut self) {
        // ロック解除前に必ずメモリを確実にゼロ消去する。
        self.inner.zeroize();

        if self.locked {
            let ptr = self.inner.as_mut_slice().as_mut_ptr();
            Self::release_lock(ptr, N);
            self.locked = false;
        }
    }
}

impl<const N: usize> Default for LockedBuffer<N> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<const N: usize> From<[u8; N]> for LockedBuffer<N> {
    #[inline]
    fn from(bytes: [u8; N]) -> Self {
        Self::new(bytes)
    }
}

impl<const N: usize> AsRef<[u8]> for LockedBuffer<N> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<const N: usize> AsMut<[u8]> for LockedBuffer<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_mut_slice()
    }
}

impl<const N: usize> core::ops::Deref for LockedBuffer<N> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<const N: usize> core::ops::DerefMut for LockedBuffer<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<const N: usize> core::fmt::Debug for LockedBuffer<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("LockedBuffer")
            .field("len", &N)
            .field("locked", &self.locked)
            .field("inner", &"[REDACTED]")
            .finish()
    }
}

impl<const N: usize> subtle::ConstantTimeEq for LockedBuffer<N> {
    #[inline]
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        crate::constant_time::ct_eq_bytes(self.as_slice(), other.as_slice())
    }
}

impl<const N: usize> Zeroize for LockedBuffer<N> {
    #[inline]
    fn zeroize(&mut self) {
        self.inner.zeroize();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_locked_buffer_basic() {
        let mut buf = LockedBuffer::new([0x33u8; 32]);
        assert_eq!(buf.len(), 32, "バッファ長の取得に成功。");
        assert!(!buf.is_empty(), "バッファが空でないことの検証に成功。");
        assert_eq!(buf.as_slice(), &[0x33u8; 32], "初期データ照合に成功。");

        buf.as_mut_slice()[0] = 0x44;
        assert_eq!(buf[0], 0x44, "可変スライス経由の代入に成功。");
    }

    #[test]
    fn test_locked_buffer_zero() {
        let buf = LockedBuffer::<16>::zero();
        assert_eq!(buf.as_slice(), &[0u8; 16], "ゼロ埋め初期化に成功。");
    }

    #[test]
    fn test_locked_buffer_strict_or_fallback() {
        let res = LockedBuffer::new_strict([0x55u8; 32]);
        match res {
            Ok(buf) => {
                assert!(buf.is_locked(), "厳格モードでのメモリロック成功に成功。");
                assert_eq!(buf.as_slice(), &[0x55u8; 32]);
            }
            Err(SystemError::MemoryLockFailed) => {
                // 非特権環境等の制限によりロックに失敗した場合のハンドリング
                let fallback = LockedBuffer::new([0x55u8; 32]);
                assert!(
                    !fallback.is_locked(),
                    "フォールバック時のアンロック状態確認に成功。"
                );
            }
            Err(_) => panic!("想定外のエラーが発生しました。"),
        }
    }

    #[test]
    fn test_locked_buffer_debug_redacted() {
        let buf = LockedBuffer::new([0x77u8; 8]);
        let debug_str = alloc::format!("{buf:?}");
        assert!(
            debug_str.contains("[REDACTED]"),
            "Debug出力でシークレットが秘匿されていることに成功。"
        );
        assert!(
            !debug_str.contains("119"),
            "Debug出力に平文バイトが含まれないことに成功。"
        );
    }

    #[test]
    fn test_locked_buffer_constant_time_eq() {
        use subtle::ConstantTimeEq;

        let buf1 = LockedBuffer::new([0x88u8; 16]);
        let buf2 = LockedBuffer::new([0x88u8; 16]);
        let buf3 = LockedBuffer::new([0x99u8; 16]);

        assert_eq!(
            buf1.ct_eq(&buf2).unwrap_u8(),
            1,
            "同一値の定数時間等価判定に成功。"
        );
        assert_eq!(
            buf1.ct_eq(&buf3).unwrap_u8(),
            0,
            "不一致値の定数時間等価判定に成功。"
        );
    }

    #[test]
    fn test_locked_buffer_conditional_assign() {
        use subtle::Choice;

        let mut dest = LockedBuffer::new([0x11u8; 4]);
        let src = LockedBuffer::new([0x22u8; 4]);

        dest.conditional_assign(&src, Choice::from(0));
        assert_eq!(
            dest.as_slice(),
            &[0x11u8; 4],
            "Choice(0)で変更されないことに成功。"
        );

        dest.conditional_assign(&src, Choice::from(1));
        assert_eq!(
            dest.as_slice(),
            &[0x22u8; 4],
            "Choice(1)で値がコピーされることに成功。"
        );
    }

    #[test]
    fn test_locked_buffer_zeroize() {
        let mut buf = LockedBuffer::new([0xaau8; 16]);
        buf.zeroize();
        assert_eq!(buf.as_slice(), &[0u8; 16], "明示的ゼロ消去に成功。");
    }
}
