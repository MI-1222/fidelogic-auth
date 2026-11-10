//! # メモリゼロ消去モジュール
//!
//! 秘密情報を保持するバッファの即時ゼロクリアと、スコープ離脱時の自動消去(RAII)を提供する。
//! `zeroize` クレートの `Zeroize`, `ZeroizeOnDrop` を活用した基盤セキュアバッファ型を定義する。

use zeroize::{Zeroize, ZeroizeOnDrop};

/// 指定された生バイトスライスを即時ゼロクリアする局所プリミティブ。
///
/// コンパイラ最適化による Dead Store Elimination (DSE) を抑止するため、
/// [`zeroize::Zeroize::zeroize`] を呼び出した上でコンパイラフェンス([`core::sync::atomic::compiler_fence`])を実行し、
/// メモリ消去命令の並べ替えや除去を確実に防止する。
#[inline(never)]
pub fn volatile_zeroize(buffer: &mut [u8]) {
    buffer.zeroize();
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// 固定長バイト配列を保持し、スコープ離脱時(Drop時)にメモリを確実にゼロ消去するセキュアバッファ。
///
/// スタック上で管理される暗号鍵(DEK/KEK等)や認証タグの保持に適しており、
/// [`zeroize::Zeroize`] および [`zeroize::ZeroizeOnDrop`] により自動消去される。
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct SecretBytes<const N: usize> {
    inner: [u8; N],
}

impl<const N: usize> SecretBytes<N> {
    /// 新しい [`SecretBytes`] を生成する。
    #[inline]
    #[must_use]
    pub const fn new(bytes: [u8; N]) -> Self {
        Self { inner: bytes }
    }

    /// ゼロ埋めされた新しい [`SecretBytes`] を生成する。
    #[inline]
    #[must_use]
    pub const fn zero() -> Self {
        Self { inner: [0u8; N] }
    }

    /// 保持するバイト列のスライス参照を取得する。
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        &self.inner
    }

    /// 保持するバイト列の可変スライス参照を取得する。
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.inner
    }

    /// 保持する固定長配列の参照を取得する。
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; N] {
        &self.inner
    }

    /// 保持する固定長配列の可変参照を取得する。
    #[inline]
    pub fn as_mut_bytes(&mut self) -> &mut [u8; N] {
        &mut self.inner
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
}

impl<const N: usize> Default for SecretBytes<N> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<const N: usize> From<[u8; N]> for SecretBytes<N> {
    #[inline]
    fn from(bytes: [u8; N]) -> Self {
        Self::new(bytes)
    }
}

impl<const N: usize> AsRef<[u8]> for SecretBytes<N> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.inner
    }
}

impl<const N: usize> AsMut<[u8]> for SecretBytes<N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.inner
    }
}

impl<const N: usize> core::ops::Deref for SecretBytes<N> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<const N: usize> core::ops::DerefMut for SecretBytes<N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<const N: usize> core::fmt::Debug for SecretBytes<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SecretBytes")
            .field("len", &N)
            .field("inner", &"[REDACTED]")
            .finish()
    }
}

/// ヒープ上に可変長バイト列を保持し、スコープ離脱時(Drop時)にメモリを確実にゼロ消去するセキュアバッファ。
///
/// 動的サイズの平文や暗号文、鍵導出中間バッファの保持に適しており、
/// [`zeroize::Zeroize`] および [`zeroize::ZeroizeOnDrop`] により破棄時にゼロクリアされる。
#[cfg(feature = "alloc")]
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct SecretVec {
    inner: alloc::vec::Vec<u8>,
}

#[cfg(feature = "alloc")]
impl SecretVec {
    /// 空の新しい [`SecretVec`] を生成する。
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            inner: alloc::vec::Vec::new(),
        }
    }

    /// 指定された容量を持つ新しい [`SecretVec`] を生成する。
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: alloc::vec::Vec::with_capacity(capacity),
        }
    }

    /// 既存の [`alloc::vec::Vec<u8>`] から [`SecretVec`] を生成する。
    #[inline]
    #[must_use]
    pub fn from_vec(vec: alloc::vec::Vec<u8>) -> Self {
        Self { inner: vec }
    }

    /// バイトスライスをコピーして新しい [`SecretVec`] を生成する。
    #[inline]
    #[must_use]
    pub fn from_slice(slice: &[u8]) -> Self {
        Self {
            inner: alloc::vec::Vec::from(slice),
        }
    }

    /// 指定された長さのゼロ埋めされた [`SecretVec`] を生成する。
    #[inline]
    #[must_use]
    pub fn zeroed(len: usize) -> Self {
        Self {
            inner: alloc::vec![0u8; len],
        }
    }

    /// 保持するバイト列のスライス参照を取得する。
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        &self.inner
    }

    /// 保持するバイト列の可変スライス参照を取得する。
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.inner
    }

    /// バッファのバイト長を返す。
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// バッファ長がゼロであるかを判定する。
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// 割り当て済みのキャパシティを返す。
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// バッファの末尾にバイトを追加する。
    #[inline]
    pub fn push(&mut self, value: u8) {
        self.inner.push(value);
    }

    /// バッファの末尾にバイトスライスを追加する。
    #[inline]
    pub fn extend_from_slice(&mut self, slice: &[u8]) {
        self.inner.extend_from_slice(slice);
    }

    /// バッファの全要素をゼロ消去した上で要素数をゼロにする。
    #[inline]
    pub fn clear(&mut self) {
        self.inner.zeroize();
    }
}

#[cfg(feature = "alloc")]
impl Default for SecretVec {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "alloc")]
impl From<alloc::vec::Vec<u8>> for SecretVec {
    #[inline]
    fn from(vec: alloc::vec::Vec<u8>) -> Self {
        Self::from_vec(vec)
    }
}

#[cfg(feature = "alloc")]
impl From<&[u8]> for SecretVec {
    #[inline]
    fn from(slice: &[u8]) -> Self {
        Self::from_slice(slice)
    }
}

#[cfg(feature = "alloc")]
impl AsRef<[u8]> for SecretVec {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.inner
    }
}

#[cfg(feature = "alloc")]
impl AsMut<[u8]> for SecretVec {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.inner
    }
}

#[cfg(feature = "alloc")]
impl core::ops::Deref for SecretVec {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[cfg(feature = "alloc")]
impl core::ops::DerefMut for SecretVec {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

#[cfg(feature = "alloc")]
impl core::fmt::Debug for SecretVec {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SecretVec")
            .field("len", &self.inner.len())
            .field("inner", &"[REDACTED]")
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_volatile_zeroize() {
        let mut secret = [0x42u8; 32];
        volatile_zeroize(&mut secret);
        assert_eq!(secret, [0u8; 32]);
    }

    #[test]
    fn test_secret_bytes_basic() {
        let mut bytes = SecretBytes::new([0xaa; 16]);
        assert_eq!(bytes.len(), 16);
        assert!(!bytes.is_empty());
        assert_eq!(bytes.as_slice(), &[0xaa; 16]);
        assert_eq!(bytes.as_bytes(), &[0xaa; 16]);

        bytes.as_mut_slice()[0] = 0xbb;
        assert_eq!(bytes[0], 0xbb);

        let default_bytes: SecretBytes<8> = SecretBytes::default();
        assert_eq!(default_bytes.as_slice(), &[0u8; 8]);
    }

    #[test]
    fn test_secret_bytes_zeroize() {
        let mut bytes = SecretBytes::new([0x55; 32]);
        bytes.zeroize();
        assert_eq!(bytes.as_slice(), &[0u8; 32]);
    }

    #[test]
    fn test_secret_bytes_debug_redacted() {
        let bytes = SecretBytes::new([0x12; 4]);
        #[cfg(feature = "alloc")]
        {
            use alloc::format;
            let debug_output = format!("{bytes:?}");
            assert!(debug_output.contains("[REDACTED]"));
            assert!(!debug_output.contains("18"));
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_secret_vec_basic() {
        let mut svec = SecretVec::from_slice(&[1, 2, 3, 4]);
        assert_eq!(svec.len(), 4);
        assert!(!svec.is_empty());
        assert_eq!(&svec[..], &[1, 2, 3, 4]);

        svec.push(5);
        assert_eq!(svec.len(), 5);
        assert_eq!(&svec[..], &[1, 2, 3, 4, 5]);

        svec.extend_from_slice(&[6, 7]);
        assert_eq!(svec.len(), 7);

        let zeroed = SecretVec::zeroed(10);
        assert_eq!(zeroed.len(), 10);
        assert_eq!(&zeroed[..], &[0u8; 10]);

        let empty = SecretVec::new();
        assert!(empty.is_empty());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_secret_vec_zeroize_and_clear() {
        let mut svec = SecretVec::from_slice(&[0x77; 16]);
        svec.clear();
        assert_eq!(svec.len(), 0);

        let mut svec2 = SecretVec::from_slice(&[0x88; 16]);
        svec2.zeroize();
        assert_eq!(svec2.len(), 0);
    }
}
