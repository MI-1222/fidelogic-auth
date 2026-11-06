//! # メモリゼロ消去モジュール
//!
//! 秘密情報を保持するバッファの即時ゼロクリアと、揮発性書き込みによるメモリ消去を提供する。

/// 指定されたバイトスライスを揮発性書き込みによりゼロクリアする。
///
/// コンパイラ最適化による Dead Store Elimination (DSE) で消去処理が除去されないよう、
/// [`core::ptr::write_volatile`] およびコンパイラフェンス（[`core::sync::atomic::compiler_fence`]）を用いて安全にゼロ埋めを行う。
#[inline(never)]
pub fn volatile_zeroize(buffer: &mut [u8]) {
    for byte in buffer.iter_mut() {
        // SAFETY: 可変スライス参照から取得したポインタへの書き込みであり、アクセス境界は有効。
        unsafe {
            core::ptr::write_volatile(byte, 0);
        }
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
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
}
