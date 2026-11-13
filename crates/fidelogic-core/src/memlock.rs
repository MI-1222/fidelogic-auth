//! # メモリロック保護モジュール(Native限定)
//!
//! DEK(データ暗号化鍵)やKEK(鍵暗号化鍵)などの極小暗号領域に対して、
//! OSレベルのメモリ保護(`libc::mlock` および `libc::madvise(MADV_DONTDUMP)` 等)を提供する。
//! スワップ領域への書き出し防止とコアダンプ生成時の機密漏洩遮断を確立し、
//! 非特権コンテナ環境等におけるフォールバック動作をサポートする。
//!
//! ## プラットフォーム別のダンプ抑止と macOS における注意
//! Linux/Android では `libc::MADV_DONTDUMP`、FreeBSD では `libc::MADV_NOCORE` により、
//! 個別ページ単位でコアダンプ書き出しを抑止する。
//! 一方で macOS (Darwin) のカーネルには個別メモリ領域単位のダンプ抑止 API が存在しないため、
//! プロセス異常終了時にコアダンプへ機密情報が残留することを防ぐには、
//! プロセス起動時または初期化時に `libc::setrlimit(libc::RLIMIT_CORE, &rlim)` で
//! コアダンプ上限サイズをゼロ (`rlim_cur = 0`, `rlim_max = 0`) に設定する等のプロセスレベルの防御が必要となる。
//!
//! ## ページ独立性に関する設計上の注意
//! Linux等のPOSIX環境において、`libc::mlock` および `libc::munlock` はシステムページ単位で動作し、
//! カーネル側にロック参照カウントを保持しない。
//! 通常のヒープアロケータ(`Box` 等)で複数の小さな鍵を隣接配置した場合、
//! 一方の `Drop` に伴う `munlock` が同一ページ上の別バッファのロックまで即座に解除してしまう問題が発生する。
//! これを構造的に防止するため、本モジュールはUnix環境において `libc::mmap` を用いて、
//! システムページ境界にアラインされた独立匿名ページ(ページサイズ単位)を専用で確保し、
//! 他の [`LockedBuffer`] や一般ヒープ領域とページを共有しない。

use alloc::boxed::Box;
#[cfg(unix)]
use core::ptr::NonNull;
use zeroize::{Zeroize, ZeroizeOnDrop};

use crate::error::SystemError;
use crate::zeroize::{SecretBytes, volatile_zeroize};

/// [`LockedBuffer`] の内部メモリ表現。
enum BufferStorage<const N: usize> {
    /// システムページ境界に独立配置され、`mlock` 保護が適用された専用匿名ページ領域。
    #[cfg(unix)]
    PageLocked { ptr: NonNull<u8>, alloc_len: usize },
    /// 通常ヒープ上のフォールバック領域(ロック失敗時、ゼロ長時、または非Unix環境)。
    HeapFallback(Box<SecretBytes<N>>),
}

/// OSレベルでページロック(スワップ防止)およびダンプ抑止が適用された固定長セキュアバッファ。
///
/// Unix環境では `libc::mmap` により他のバッファや通常ヒープとページを共有しない独立ページ上に配置され、
/// 破棄時(`Drop`)には内部メモリを即座にゼロ消去した上で `libc::munlock` および `libc::munmap` を実行する。
/// そのため、あるインスタンスの破棄が他の [`LockedBuffer`] のメモリロックを早期解除することはない。
///
/// # リソース消費およびコアダンプ抑止に関する注意
/// 各インスタンスは独立性を保証するため、最低1システムページ(通常4 KiB〜16 KiB)の仮想メモリと
/// `RLIMIT_MEMLOCK` クォータを消費する。DEKやKEKなど、少数の極小暗号鍵専用として使用すること。
///
/// Linux/Android/FreeBSD では `madvise` により対象ページがコアダンプから除外されるが、
/// macOS では個別メモリ領域のダンプ抑止フラグが存在しないため、
/// プロセス側で `RLIMIT_CORE = 0` を設定してコアダンプ生成自体を無効化する必要がある。
///
/// 非特権環境等で `mlock` に失敗してフォールバック生成された場合(`is_locked() == false`)は、
/// 通常ヒープへ格納され、破棄時に `munlock` は実行されない。
pub struct LockedBuffer<const N: usize> {
    storage: BufferStorage<N>,
    locked: bool,
}

// SAFETY: `LockedBuffer<N>` は内部のバッファ領域を排他的に所有し、
// 共有参照からは不変アクセスのみ、変更には排他的可変参照(`&mut self`)を要求するため、
// スレッド間での所有権移動(Send)および共有参照の送信(Sync)は安全である。
unsafe impl<const N: usize> Send for LockedBuffer<N> {}
unsafe impl<const N: usize> Sync for LockedBuffer<N> {}

impl<const N: usize> LockedBuffer<N> {
    /// 新しい [`LockedBuffer`] を生成し、メモリロック保護を適用する。
    ///
    /// 非特権環境やリソース制限によりメモリロックに失敗した場合は、
    /// アンロック状態のセキュアバッファとしてフォールバック生成する(呼び出し側で [`Self::is_locked`] を検査可能)。
    /// メモリロック失敗を許容しない場合は [`Self::new_strict`] を使用すること。
    ///
    /// # 注意
    /// 値渡しされた引数配列の内部バッファは生成処理完了時にゼロ消去されるが、
    /// 呼び出し元スタックフレーム上の元の配列がコピーされている場合、呼び出し元側のスタック残留は防げない。
    /// 呼び出し元バッファを確実に消費・消去するには [`Self::from_consumed_secret`] の使用を推奨する。
    #[must_use]
    pub fn new(mut bytes: [u8; N]) -> Self {
        let mut secret = SecretBytes::new(bytes);
        volatile_zeroize(&mut bytes);
        Self::from_consumed_secret(&mut secret)
    }

    /// 呼び出し元の [`SecretBytes<N>`] からデータをコピーして [`LockedBuffer`] を生成し、
    /// コピー完了後に呼び出し元の秘密バッファを即座にゼロ消去する。
    ///
    /// 呼び出し元のスタック上に平文秘密情報が残留することを構造的に防止する。
    /// 非特権環境やリソース制限によりメモリロックに失敗した場合は、
    /// アンロック状態のセキュアバッファとしてフォールバック生成する(呼び出し側で [`Self::is_locked`] を検査可能)。
    /// メモリロック失敗を許容しない場合は [`Self::try_from_consumed_secret`] を使用すること。
    #[must_use]
    pub fn from_consumed_secret(secret: &mut SecretBytes<N>) -> Self {
        secret.consume_with(|bytes| {
            if N == 0 {
                return Self {
                    storage: BufferStorage::HeapFallback(Box::new(SecretBytes::new([0u8; N]))),
                    locked: false,
                };
            }

            match Self::try_allocate_page_locked(bytes) {
                Ok(storage) => Self {
                    storage,
                    locked: true,
                },
                Err(_errno) => {
                    let inner = Box::new(SecretBytes::new(*bytes));
                    Self {
                        storage: BufferStorage::HeapFallback(inner),
                        locked: false,
                    }
                }
            }
        })
    }

    /// 厳格なセキュリティポリシーのもとで新しい [`LockedBuffer`] を生成する。
    ///
    /// メモリロックまたはダンプ抑止の適用に失敗した場合はフォールバックを行わず、
    /// 即座に [`SystemError::MemoryLockFailed`] を返却する。
    ///
    /// # 注意
    /// 呼び出し元バッファを確実に消費・消去するには [`Self::try_from_consumed_secret`] の使用を推奨する。
    ///
    /// # エラー
    /// OSシステムコール(`mmap`, `mlock` 等)が失敗した場合に [`SystemError::MemoryLockFailed`] を返す。
    pub fn new_strict(mut bytes: [u8; N]) -> Result<Self, SystemError> {
        let mut secret = SecretBytes::new(bytes);
        volatile_zeroize(&mut bytes);
        Self::try_from_consumed_secret(&mut secret)
    }

    /// 厳格なセキュリティポリシーのもとで呼び出し元の [`SecretBytes<N>`] からデータをコピーし、
    /// コピー完了後に呼び出し元の秘密バッファを即座にゼロ消去する。
    ///
    /// メモリロックまたはダンプ抑止の適用に失敗した場合はフォールバックを行わず、
    /// 即座に [`SystemError::MemoryLockFailed`] を返却する(その場合も呼び出し元の秘密バッファは確実にゼロ消去される)。
    ///
    /// # エラー
    /// OSシステムコール(`mmap`, `mlock` 等)が失敗した場合に [`SystemError::MemoryLockFailed`] を返す。
    pub fn try_from_consumed_secret(secret: &mut SecretBytes<N>) -> Result<Self, SystemError> {
        secret.consume_with(|bytes| {
            if N == 0 {
                return Ok(Self {
                    storage: BufferStorage::HeapFallback(Box::new(SecretBytes::new([0u8; N]))),
                    locked: false,
                });
            }

            match Self::try_allocate_page_locked(bytes) {
                Ok(storage) => Ok(Self {
                    storage,
                    locked: true,
                }),
                Err(_errno) => Err(SystemError::MemoryLockFailed),
            }
        })
    }

    /// ゼロ埋めされた新しい [`LockedBuffer`] を生成する(非特権環境フォールバック付き)。
    #[must_use]
    pub fn zero() -> Self {
        Self::new([0u8; N])
    }

    /// ゼロ埋めされた新しい [`LockedBuffer`] を厳格モードで生成する。
    ///
    /// # エラー
    /// OSシステムコール(`mmap`, `mlock` 等)が失敗した場合に [`SystemError::MemoryLockFailed`] を返す。
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
        match &self.storage {
            #[cfg(unix)]
            BufferStorage::PageLocked { ptr, .. } => {
                // SAFETY: `PageLocked` は少なくとも `N` バイトの初期化済み領域を指しており、
                // `LockedBuffer` の生存期間中かつ解放前まで有効である。
                unsafe { core::slice::from_raw_parts(ptr.as_ptr(), N) }
            }
            BufferStorage::HeapFallback(inner) => inner.as_slice(),
        }
    }

    /// 保持するバイト列の可変スライス参照を取得する。
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        match &mut self.storage {
            #[cfg(unix)]
            BufferStorage::PageLocked { ptr, .. } => {
                // SAFETY: `&mut self` により排他的アクセスが保証されており、
                // 少なくとも `N` バイトの初期化済みRW領域を指している。
                unsafe { core::slice::from_raw_parts_mut(ptr.as_ptr(), N) }
            }
            BufferStorage::HeapFallback(inner) => inner.as_mut_slice(),
        }
    }

    /// 保持する固定長配列の参照を取得する。
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; N] {
        match &self.storage {
            #[cfg(unix)]
            BufferStorage::PageLocked { ptr, .. } => {
                // SAFETY: `ptr` は先頭 `N` バイトが初期化済みで、
                // `[u8; N]` のアラインメント要件(1バイト)を満たしている。
                unsafe { &*ptr.as_ptr().cast::<[u8; N]>() }
            }
            BufferStorage::HeapFallback(inner) => inner.as_bytes(),
        }
    }

    /// 保持する固定長配列の可変参照を取得する。
    #[inline]
    pub fn as_mut_bytes(&mut self) -> &mut [u8; N] {
        match &mut self.storage {
            #[cfg(unix)]
            BufferStorage::PageLocked { ptr, .. } => {
                // SAFETY: `&mut self` により排他的アクセスが保証され、
                // `[u8; N]` のアラインメント要件(1バイト)および初期化条件を満たしている。
                unsafe { &mut *ptr.as_ptr().cast::<[u8; N]>() }
            }
            BufferStorage::HeapFallback(inner) => inner.as_mut_bytes(),
        }
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
        crate::constant_time::ct_assign_slice(choice, self.as_mut_slice(), other.as_slice());
    }

    /// ページ単位の独立匿名メモリを割り当て、データ書き込み前にメモリロック保護を適用する。
    #[cfg(unix)]
    fn try_allocate_page_locked(bytes: &[u8; N]) -> Result<BufferStorage<N>, i32> {
        let page_size = Self::system_page_size()?;
        let alloc_len = N.checked_next_multiple_of(page_size).ok_or(libc::ENOMEM)?;

        // 他のヒープ領域や他インスタンスとページを共有しないよう、独立した匿名ページを確保する。
        let raw_ptr = unsafe {
            libc::mmap(
                core::ptr::null_mut(),
                alloc_len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            )
        };
        if raw_ptr == libc::MAP_FAILED {
            return Err(Self::last_os_errno());
        }

        let Some(ptr) = NonNull::new(raw_ptr.cast::<u8>()) else {
            unsafe {
                let _ = libc::munmap(raw_ptr, alloc_len);
            }
            return Err(libc::ENOMEM);
        };

        // 秘密データを書き込む前にページロックとコアダンプ抑止を適用する。
        if let Err(errno) = Self::apply_lock(ptr.as_ptr(), alloc_len) {
            unsafe {
                let _ = libc::munmap(ptr.as_ptr().cast::<libc::c_void>(), alloc_len);
            }
            return Err(errno);
        }

        // SAFETY: `ptr` は `alloc_len >= N` バイトのRW可能な新規匿名マッピングを指し、
        // `bytes` とは重ならない。
        unsafe {
            core::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr.as_ptr(), N);
        }

        Ok(BufferStorage::PageLocked { ptr, alloc_len })
    }

    /// 非Unix環境向けスタブ(フォールバックを促す)。
    #[cfg(not(unix))]
    fn try_allocate_page_locked(_bytes: &[u8; N]) -> Result<BufferStorage<N>, i32> {
        Err(-1)
    }

    /// OSのシステムページサイズ(バイト数)を取得する。
    #[cfg(unix)]
    fn system_page_size() -> Result<usize, i32> {
        let raw = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        if raw <= 0 {
            return Err(Self::last_os_errno());
        }
        let page_size = raw as usize;
        if !page_size.is_power_of_two() {
            return Err(libc::EINVAL);
        }
        Ok(page_size)
    }

    /// 直近のOSエラー番号を取得する。
    #[cfg(unix)]
    fn last_os_errno() -> i32 {
        std::io::Error::last_os_error().raw_os_error().unwrap_or(-1)
    }

    /// 指定されたページアライン済みメモリ領域に対して `mlock` および `madvise` を適用する。
    ///
    /// # コアダンプ抑止のプラットフォーム差異
    /// - Linux/Android: `libc::MADV_DONTDUMP` を適用し、コアダンプから除外する。
    /// - FreeBSD: `libc::MADV_NOCORE` を適用し、コアダンプから除外する。
    /// - macOS (Darwin): メモリ領域単位でのダンプ抑止フラグが存在しないため、
    ///   プロセス側で `RLIMIT_CORE = 0` を設定する等の併用が必要となる。
    #[allow(unused_variables)]
    fn apply_lock(ptr: *mut u8, len: usize) -> Result<(), i32> {
        if len == 0 {
            return Ok(());
        }

        #[cfg(unix)]
        {
            let void_ptr = ptr.cast::<libc::c_void>();
            // メモリページを物理RAMに固定し、スワップアウトを防止する。
            let ret = unsafe { libc::mlock(void_ptr, len) };
            if ret != 0 {
                return Err(Self::last_os_errno());
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

    /// 指定されたページアライン済みメモリ領域の `mlock` ロックを解除する。
    #[allow(unused_variables)]
    fn release_lock(ptr: *mut u8, len: usize) {
        if len == 0 {
            return;
        }

        #[cfg(unix)]
        unsafe {
            let void_ptr = ptr.cast::<libc::c_void>();
            let _ = libc::munlock(void_ptr, len);
        }
    }
    /// 内部ストレージの確保済み領域全体(パディング領域を含む)を即時ゼロ消去する。
    #[inline]
    fn zeroize_backing_storage(&mut self) {
        match &mut self.storage {
            #[cfg(unix)]
            BufferStorage::PageLocked { ptr, alloc_len } => {
                // SAFETY: `&mut self` により排他的アクセスが保証されており、
                // `ptr` は `mmap` で確保された `alloc_len` バイトのRW可能な有効領域を指している。
                let full_page =
                    unsafe { core::slice::from_raw_parts_mut(ptr.as_ptr(), *alloc_len) };
                volatile_zeroize(full_page);
            }
            BufferStorage::HeapFallback(inner) => {
                volatile_zeroize(inner.as_mut_slice());
            }
        }
    }
}

impl<const N: usize> Drop for LockedBuffer<N> {
    fn drop(&mut self) {
        // ロック解除およびメモリ解放の前に、パディング領域を含む確保済みメモリ全体を確実にゼロ消去する。
        self.zeroize_backing_storage();

        #[cfg(unix)]
        if let BufferStorage::PageLocked { ptr, alloc_len } = self.storage {
            if self.locked {
                Self::release_lock(ptr.as_ptr(), alloc_len);
                self.locked = false;
            }
            unsafe {
                let _ = libc::munmap(ptr.as_ptr().cast::<libc::c_void>(), alloc_len);
            }
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
    type Target = [u8; N];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_bytes()
    }
}

impl<const N: usize> core::ops::DerefMut for LockedBuffer<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_bytes()
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
        crate::constant_time::ct_eq_array(self.as_bytes(), other.as_bytes())
    }
}

impl<const N: usize> Zeroize for LockedBuffer<N> {
    #[inline]
    fn zeroize(&mut self) {
        self.zeroize_backing_storage();
    }
}

impl<const N: usize> ZeroizeOnDrop for LockedBuffer<N> {}

const _: fn() = || {
    fn assert_zeroize_on_drop<T: ZeroizeOnDrop>() {}
    assert_zeroize_on_drop::<LockedBuffer<0>>();
    assert_zeroize_on_drop::<LockedBuffer<32>>();
};

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
    fn test_locked_buffer_zero_length() {
        let mut buf = LockedBuffer::<0>::new([]);
        assert_eq!(buf.len(), 0, "ゼロ長バッファの長さ取得に成功。");
        assert!(buf.is_empty(), "ゼロ長バッファの空判定に成功。");
        assert!(
            !buf.is_locked(),
            "ゼロ長バッファがアンロック状態であることの検証に成功。"
        );
        buf.zeroize();

        let strict = LockedBuffer::<0>::new_strict([]).expect("ゼロ長バッファの厳格生成に成功。");
        assert!(!strict.is_locked());
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

    #[cfg(unix)]
    #[test]
    fn test_locked_buffer_page_isolation_and_no_early_unlock() {
        let dek = LockedBuffer::new([0x12u8; 32]);
        let mut kek = LockedBuffer::new([0x34u8; 32]);

        if dek.is_locked() && kek.is_locked() {
            let page_size =
                LockedBuffer::<32>::system_page_size().expect("システムページサイズの取得に成功。");
            let dek_addr = dek.as_ptr() as usize;
            let kek_addr = kek.as_ptr() as usize;

            assert_eq!(
                dek_addr % page_size,
                0,
                "DEKバッファがページ境界にアラインされていることの検証に成功。"
            );
            assert_eq!(
                kek_addr % page_size,
                0,
                "KEKバッファがページ境界にアラインされていることの検証に成功。"
            );
            assert_ne!(
                dek_addr / page_size,
                kek_addr / page_size,
                "DEKとKEKが異なる仮想ページに分離配置されていることの検証に成功。"
            );

            // DEKを破棄(munlock + munmap)しても、別ページのKEKのロックは解除されない。
            drop(dek);
            assert!(
                kek.is_locked(),
                "DEK破棄後もKEKのロック状態が維持されていることの検証に成功。"
            );
            assert_eq!(kek.as_bytes(), &[0x34u8; 32]);
            kek.as_mut_bytes()[31] = 0x56;
            assert_eq!(kek[31], 0x56);
        }
    }

    #[test]
    fn test_locked_buffer_multi_page_allocation() {
        let mut buf = LockedBuffer::new([0xabu8; 32768]);
        assert_eq!(buf.len(), 32768);
        assert_eq!(buf[0], 0xab);
        assert_eq!(buf[32767], 0xab);

        buf.as_mut_slice()[32767] = 0xcd;
        assert_eq!(buf[32767], 0xcd);
        buf.zeroize();
        assert_eq!(buf[0], 0);
        assert_eq!(buf[32767], 0);
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

    #[test]
    fn test_locked_buffer_deref_array() {
        fn accept_array(arr: &[u8; 16]) -> u8 {
            arr[0]
        }
        fn accept_mut_array(arr: &mut [u8; 16], val: u8) {
            arr[1] = val;
        }
        fn accept_slice(slice: &[u8]) -> usize {
            slice.len()
        }
        fn accept_mut_slice(slice: &mut [u8], val: u8) {
            slice[2] = val;
        }

        let mut buf = LockedBuffer::new([0x11u8; 16]);

        let array_ref: &[u8; 16] = &buf;
        assert_eq!(array_ref, &[0x11u8; 16], "固定長配列参照へのDerefに成功。");
        assert_eq!(accept_array(&buf), 0x11, "固定長配列引数の自動変換に成功。");
        assert_eq!(
            accept_slice(&*buf),
            16,
            "明示的デリファレンス経由のスライス変換に成功。"
        );
        assert_eq!(
            accept_slice(buf.as_ref()),
            16,
            "AsRef経由のスライス変換に成功。"
        );

        let mut_array_ref: &mut [u8; 16] = &mut buf;
        mut_array_ref[0] = 0x22;
        accept_mut_array(&mut buf, 0x33);
        accept_mut_slice(&mut *buf, 0x44);

        assert_eq!(buf[0], 0x22, "可変固定長配列参照経由の更新に成功。");
        assert_eq!(buf[1], 0x33, "可変固定長配列引数の更新に成功。");
        assert_eq!(
            buf[2], 0x44,
            "明示的デリファレンス経由の可変スライス更新に成功。"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_locked_buffer_page_locked_padding_zeroize() {
        let mut buf = LockedBuffer::new([0xaau8; 32]);
        if let BufferStorage::PageLocked { ptr, alloc_len } = buf.storage {
            assert!(
                alloc_len > 32,
                "ページサイズ単位のアロケーションによりパディング領域が存在することの確認に成功。"
            );

            // パディング領域(Nバイト目〜alloc_len-1バイト目)に意図的に非ゼロ値を書き込み、
            // 領域全体がゼロ消去されることを検証する。
            unsafe {
                let full_page = core::slice::from_raw_parts_mut(ptr.as_ptr(), alloc_len);
                full_page[32..].fill(0x55);
            }

            buf.zeroize();

            let full_page = unsafe { core::slice::from_raw_parts(ptr.as_ptr(), alloc_len) };
            assert!(
                full_page.iter().all(|&b| b == 0),
                "データ領域とパディング領域を含むページ全体のゼロ消去に成功。"
            );
        }
    }

    #[test]
    fn test_locked_buffer_from_consumed_secret() {
        let mut secret = SecretBytes::new([0x42u8; 32]);
        let buf = LockedBuffer::from_consumed_secret(&mut secret);
        assert_eq!(buf.len(), 32, "生成されたLockedBufferの長さ照合に成功。");
        assert_eq!(
            buf.as_slice(),
            &[0x42u8; 32],
            "LockedBufferへのデータ移管に成功。"
        );
        assert_eq!(
            secret.as_slice(),
            &[0u8; 32],
            "呼び出し元SecretBytesの消費後ゼロ消去に成功。"
        );
    }

    #[test]
    fn test_locked_buffer_try_from_consumed_secret() {
        let mut secret = SecretBytes::new([0x5au8; 32]);
        let res = LockedBuffer::try_from_consumed_secret(&mut secret);
        assert_eq!(
            secret.as_slice(),
            &[0u8; 32],
            "呼び出し元SecretBytesの消費後ゼロ消去に成功。"
        );
        match res {
            Ok(buf) => {
                assert_eq!(
                    buf.as_slice(),
                    &[0x5au8; 32],
                    "厳格モードでのデータ照合に成功。"
                );
            }
            Err(SystemError::MemoryLockFailed) => {
                // 非特権環境等でロック失敗した場合のエラーハンドリング検証
            }
            Err(_) => panic!("想定外のエラーが発生しました。"),
        }
    }

    #[test]
    fn test_locked_buffer_consumed_secret_zero_length() {
        let mut secret = SecretBytes::new([]);
        let buf = LockedBuffer::<0>::from_consumed_secret(&mut secret);
        assert_eq!(buf.len(), 0, "ゼロ長バッファの生成に成功。");
        assert_eq!(secret.as_slice(), &[], "ゼロ長秘密情報の消費に成功。");

        let mut strict_secret = SecretBytes::new([]);
        let strict_buf = LockedBuffer::<0>::try_from_consumed_secret(&mut strict_secret)
            .expect("ゼロ長バッファの厳格生成に成功。");
        assert_eq!(strict_buf.len(), 0);
        assert_eq!(strict_secret.as_slice(), &[]);
    }
}
