#!/usr/bin/env bash
# `no_std` 環境でのコンパイル健全性を検証するスクリプト。
# `wasm32-unknown-unknown` ターゲットにおいて `std` の混入が発生していないかを検査する。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
cd "${REPO_ROOT}"

echo "==> [1/3] Checking fidelogic-core with default features disabled (no_std baseline)..."
cargo check -p fidelogic-core --target wasm32-unknown-unknown --no-default-features

echo "==> [2/3] Checking fidelogic-core with profile-lite (no_std)..."
cargo check -p fidelogic-core --target wasm32-unknown-unknown --no-default-features --features profile-lite

echo "==> [3/3] Checking fidelogic-core with profile-vault (no_std)..."
cargo check -p fidelogic-core --target wasm32-unknown-unknown --no-default-features --features profile-vault

echo "==> [SUCCESS] All no_std target checks passed successfully."
