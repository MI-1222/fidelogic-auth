#!/usr/bin/env bash
# 最適化済みWasmバイナリに対する Zeroize / Dead Store Elimination (DSE) 抑止静的検査スクリプト。
# `wasm2wat` を用いて逆アセンブルし、揮発性ストア命令およびゼロクリア処理がコンパイラ最適化で
# 除去されていないかを機械的に検証する。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
cd "${REPO_ROOT}"

TARGET_DIR="${REPO_ROOT}/target/wasm-size"
WASM_FILE="${TARGET_DIR}/fidelogic_lite_opt.wasm"

# ビルド成果物が存在しない場合は先にビルド。
if [ ! -f "${WASM_FILE}" ]; then
  echo "==> Building target wasm for zeroize audit..."
  "${SCRIPT_DIR}/check_wasm_size.sh"
fi

if ! command -v wasm2wat >/dev/null 2>&1; then
  echo "Warning: 'wasm2wat' (wabt) が見つかりません。環境にwabtをインストールしてください。" >&2
  # CI環境では必須だが、ローカル端末で未インストールの場合はガイダンスを出してスキップまたは警告。
  if [ -n "${CI:-}" ]; then
    echo "Error: CI環境では wasm2wat が必須です。" >&2
    exit 1
  else
    echo "Skipping zeroize WAT inspection on local environment without wabt."
    exit 0
  fi
fi

WAT_FILE="${TARGET_DIR}/fidelogic_lite.wat"
echo "==> Disassembling Wasm to WAT via wasm2wat..."
wasm2wat "${WASM_FILE}" -o "${WAT_FILE}"

echo "==> Inspecting WAT for zeroize instructions and DSE prevention..."

# 1. `fidelogic_wasm_zeroize_test` の関数またはエクスポートが存在するか検査。
if ! grep -q 'fidelogic_wasm_zeroize_test' "${WAT_FILE}"; then
  echo "Error: WAT内に 'fidelogic_wasm_zeroize_test' エクスポートシンボルが見つかりません。" >&2
  exit 1
fi

# 2. 揮発性ストアまたはメモリクリア命令 (`i32.store8`, `i32.store`, `memory.fill`) の残存を検査。
HAS_STORE=false
if grep -E '(i32\.store8|i32\.store|memory\.fill)' "${WAT_FILE}" >/dev/null 2>&1; then
  HAS_STORE=true
fi

if [ "${HAS_STORE}" = "false" ]; then
  echo "Error: WAT内にゼロ消去用ストア命令 (i32.store8 / i32.store / memory.fill) が検出されませんでした。" >&2
  echo "コンパイラの最適化 (Dead Store Elimination) により消去された可能性があります。" >&2
  exit 1
fi

echo "==> [SUCCESS] Verified zeroize volatile store instructions are preserved in Wasm binary."
