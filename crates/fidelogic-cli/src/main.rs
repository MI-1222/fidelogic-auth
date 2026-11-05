//! # fidelogic-cli
//!
//! Fidelogic Vaultのローカル運用, 鍵管理を行うネイティブCLIツール。

use fidelogic_core::active_profile;

fn main() {
    println!("fidelogic-cli (fidelogic-core: {})", active_profile());
}
