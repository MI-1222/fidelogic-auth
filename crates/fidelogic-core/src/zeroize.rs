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

/// 指定された 32-bit ワード列スライス (Unicode コードポイント等) を即時ゼロクリアする局所プリミティブ。
///
/// コンパイラ最適化による Dead Store Elimination (DSE) を抑止するため、
/// [`zeroize::Zeroize::zeroize`] を呼び出した上でコンパイラフェンス([`core::sync::atomic::compiler_fence`])を実行し、
/// メモリ消去命令の並べ替えや除去を確実に防止する。
#[inline(never)]
pub fn volatile_zeroize_words(buffer: &mut [u32]) {
    buffer.zeroize();
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// 指定ポインタ先頭から `len` バイトの領域(未初期化パディング領域を含む)を揮発性ゼロ書込みで消去する。
///
/// 列挙型やアラインメントパディング等の未初期化バイトを含みうる領域に対し、
/// `&mut [u8]` 参照を生成せずにバイト単位で `0x00` を書き込み、Dead Store Elimination を抑止する。
///
/// # 安全性
/// `ptr` は少なくとも `len` バイトの書き込み可能な連続メモリ領域を指している必要がある。
#[cfg_attr(not(feature = "profile-vault"), allow(dead_code))]
#[inline(never)]
pub(crate) unsafe fn volatile_zeroize_raw(ptr: *mut u8, len: usize) {
    let mut offset = 0usize;
    while offset < len {
        unsafe { core::ptr::write_volatile(ptr.add(offset), 0u8) };
        offset += 1;
    }
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

    /// 条件 `choice` に基づき、定数時間で `other` の内容を自身に上書きコピーする。
    ///
    /// `choice` が真(`Choice(1)`)のときは `other` の内容がコピーされ、
    /// 偽(`Choice(0)`)のときは自身の値がそのまま保持される。
    #[inline]
    pub fn conditional_assign(&mut self, other: &Self, choice: subtle::Choice) {
        crate::constant_time::ct_assign_slice(choice, self.as_mut_slice(), other.as_slice());
    }

    /// 保持するバイト配列の不変参照を受け取るクロージャを実行し、完了直後に自身をゼロ消去する。
    ///
    /// クロージャの実行が正常終了した場合はもちろん、早期脱出やパニックが発生した場合でも、
    /// RAII ガードにより確実に [`volatile_zeroize`] が実行されることを保証する。
    #[inline]
    pub fn consume_with<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&[u8; N]) -> R,
    {
        struct ConsumeGuard<'a, const M: usize>(&'a mut [u8; M]);

        impl<'a, const M: usize> Drop for ConsumeGuard<'a, M> {
            #[inline]
            fn drop(&mut self) {
                volatile_zeroize(self.0);
            }
        }

        let guard = ConsumeGuard(&mut self.inner);
        f(&*guard.0)
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
    type Target = [u8; N];

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

impl<const N: usize> subtle::ConstantTimeEq for SecretBytes<N> {
    #[inline]
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        crate::constant_time::ct_eq_array(self.as_bytes(), other.as_bytes())
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

    /// 追加で少なくとも `additional` バイトを格納できるよう容量を確保する。
    ///
    /// キャパシティの拡張(再割り当て)が必要な場合、標準の `Vec::reserve` は
    /// 旧ヒープ領域をゼロ消去せずに解放(`dealloc`)して平文断片を残留させる恐れがあるため、
    /// 本メソッドでは自前で新バッファを確保した上で、旧バッファの全容量(`capacity`)を
    /// [`volatile_zeroize_raw`] により確実に揮発性ゼロ消去してからアロケータへ解放する。
    pub fn reserve(&mut self, additional: usize) {
        let needed = match self.inner.len().checked_add(additional) {
            Some(n) => n,
            None => panic!("SecretVec capacity overflow"),
        };
        if needed > self.inner.capacity() {
            // アロケーション頻度低減のため 2 倍成長を採用する。
            let new_cap = needed.max(self.inner.capacity().saturating_mul(2)).max(8);
            self.reallocate_and_zeroize_old(new_cap);
        }
    }

    /// 追加で正確に `additional` バイトを格納できるよう容量を確保する。
    ///
    /// 拡張時は [`Self::reserve`] と同様に旧ヒープ領域をゼロ消去した上で解放する。
    pub fn reserve_exact(&mut self, additional: usize) {
        let needed = match self.inner.len().checked_add(additional) {
            Some(n) => n,
            None => panic!("SecretVec capacity overflow"),
        };
        if needed > self.inner.capacity() {
            self.reallocate_and_zeroize_old(needed);
        }
    }

    fn reallocate_and_zeroize_old(&mut self, new_cap: usize) {
        let mut new_vec = alloc::vec::Vec::with_capacity(new_cap);
        new_vec.extend_from_slice(&self.inner);

        let mut old_vec = core::mem::replace(&mut self.inner, new_vec);
        let old_cap = old_vec.capacity();
        if old_cap > 0 {
            // SAFETY: old_vec は直前まで有効な Vec であり、old_cap バイトの書き込み可能な領域を持つ。
            unsafe {
                volatile_zeroize_raw(old_vec.as_mut_ptr(), old_cap);
            }
        }
        // old_vec はここで解放されるが、領域全体が事前にゼロクリアされている。
    }

    /// バッファの末尾にバイトを追加する。
    ///
    /// キャパシティ不足時の再割り当てでは、旧領域のメモリを確実にゼロ消去した上で
    /// 新領域へ移行する。
    #[inline]
    pub fn push(&mut self, value: u8) {
        if self.inner.len() == self.inner.capacity() {
            self.reserve(1);
        }
        self.inner.push(value);
    }

    /// バッファの末尾にバイトスライスを追加する。
    ///
    /// キャパシティ不足時の再割り当てでは、旧領域のメモリを確実にゼロ消去した上で
    /// 新領域へ移行する。
    #[inline]
    pub fn extend_from_slice(&mut self, slice: &[u8]) {
        let remaining = self.inner.capacity().saturating_sub(self.inner.len());
        if slice.len() > remaining {
            self.reserve(slice.len());
        }
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

#[cfg(feature = "alloc")]
impl subtle::ConstantTimeEq for SecretVec {
    #[inline]
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        crate::constant_time::ct_eq_bytes(self.as_slice(), other.as_slice())
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
    fn test_volatile_zeroize_words() {
        let mut words = [0x1234_5678u32; 16];
        volatile_zeroize_words(&mut words);
        assert_eq!(words, [0u32; 16]);
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

    #[test]
    fn test_secret_bytes_deref_array() {
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

        let mut bytes = SecretBytes::new([0x11u8; 16]);

        let array_ref: &[u8; 16] = &bytes;
        assert_eq!(array_ref, &[0x11u8; 16], "固定長配列参照へのDerefに成功。");
        assert_eq!(
            accept_array(&bytes),
            0x11,
            "固定長配列引数の自動変換に成功。"
        );
        assert_eq!(
            accept_slice(&*bytes),
            16,
            "明示的デリファレンス経由のスライス変換に成功。"
        );
        assert_eq!(
            accept_slice(&bytes[..]),
            16,
            "範囲インデックス経由のスライス変換に成功。"
        );
        assert_eq!(
            accept_slice(bytes.as_ref()),
            16,
            "AsRef経由のスライス変換に成功。"
        );

        let mut_array_ref: &mut [u8; 16] = &mut bytes;
        mut_array_ref[0] = 0x22;
        accept_mut_array(&mut bytes, 0x33);
        accept_mut_slice(&mut *bytes, 0x44);
        assert_eq!(
            bytes[2], 0x44,
            "明示的デリファレンス経由の可変スライス更新に成功。"
        );
        accept_mut_slice(bytes.as_mut(), 0x55);

        assert_eq!(bytes[0], 0x22, "可変固定長配列参照経由の更新に成功。");
        assert_eq!(bytes[1], 0x33, "可変固定長配列引数の更新に成功。");
        assert_eq!(bytes[2], 0x55, "AsMut経由の可変スライス更新に成功。");
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

    #[cfg(feature = "alloc")]
    #[test]
    fn test_secret_vec_reserve_and_growth() {
        let mut svec = SecretVec::new();
        assert_eq!(svec.capacity(), 0);

        svec.reserve(10);
        assert!(svec.capacity() >= 10);
        let cap_before = svec.capacity();

        svec.extend_from_slice(&[1, 2, 3]);
        assert_eq!(svec.as_slice(), &[1, 2, 3]);
        assert_eq!(svec.capacity(), cap_before);

        // 既存キャパシティを超える拡張
        svec.reserve_exact(cap_before + 20);
        assert!(svec.capacity() >= svec.len() + cap_before + 20);
        assert_eq!(svec.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn test_secret_bytes_consume_with() {
        let mut secret = SecretBytes::new([0x37u8; 16]);
        let read_val = secret.consume_with(|bytes| {
            assert_eq!(bytes, &[0x37u8; 16], "クロージャ内での秘密配列参照に成功。");
            bytes[0]
        });
        assert_eq!(read_val, 0x37);
        assert_eq!(secret.as_bytes(), &[0u8; 16], "消費後のゼロ消去に成功。");
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_secret_bytes_consume_with_panic_safety() {
        let mut secret = SecretBytes::new([0x55u8; 16]);
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            secret.consume_with(|bytes| {
                assert_eq!(bytes[0], 0x55);
                panic!("意図的なパニックテスト");
            });
        }));
        assert!(res.is_err(), "パニックの捕捉に成功。");
        assert_eq!(
            secret.as_bytes(),
            &[0u8; 16],
            "パニック発生時でもRAIIガードによるゼロ消去に成功。"
        );
    }
}
