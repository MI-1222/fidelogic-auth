#!/usr/bin/env bash
# Wasmバイナリの最適化および静的容量上限の判定スクリプト。
# `profile-lite` (Raw < 70KB) および `profile-vault` (Raw < 220KB) のサイズ超過を機械的に遮断する。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
cd "${REPO_ROOT}"

TARGET_DIR="${REPO_ROOT}/target/wasm-size"
mkdir -p "${TARGET_DIR}"

MAX_LITE_RAW=70000       # 70 KB
MAX_VAULT_RAW=225280     # 220 KB
MAX_LITE_WIRE=25600      # 25 KB
MAX_VAULT_WIRE=71680     # 70 KB

echo "==> [1/4] Building fidelogic-wasm (profile-lite)..."
cargo build -p fidelogic-wasm \
  --target wasm32-unknown-unknown \
  --release \
  --no-default-features \
  --features profile-lite,ci-inspection \
  --target-dir "${TARGET_DIR}/lite_build"

RAW_LITE_BIN="${TARGET_DIR}/lite_build/wasm32-unknown-unknown/release/fidelogic_wasm.wasm"
OPT_LITE_BIN="${TARGET_DIR}/fidelogic_lite_opt.wasm"

echo "==> [2/4] Building fidelogic-wasm (profile-vault)..."
cargo build -p fidelogic-wasm \
  --target wasm32-unknown-unknown \
  --release \
  --no-default-features \
  --features profile-vault,ci-inspection \
  --target-dir "${TARGET_DIR}/vault_build"

RAW_VAULT_BIN="${TARGET_DIR}/vault_build/wasm32-unknown-unknown/release/fidelogic_wasm.wasm"
OPT_VAULT_BIN="${TARGET_DIR}/fidelogic_vault_opt.wasm"

# 最適化 (`wasm-opt`) の適用。
# Rust の wasm32-unknown-unknown ターゲット標準機能セット
# (bulk-memory, sign-ext, nontrapping-float-to-int)
# の検証エラーを防ぐため、対応する feature flag を明示指定。
if command -v wasm-opt >/dev/null 2>&1; then
  echo "==> Applying wasm-opt -Oz to Lite profile..."
  wasm-opt -Oz --enable-bulk-memory --enable-sign-ext --enable-nontrapping-float-to-int \
    --strip-debug --strip-producers --vacuum "${RAW_LITE_BIN}" -o "${OPT_LITE_BIN}"

  echo "==> Applying wasm-opt -Oz to Vault profile..."
  wasm-opt -Oz --enable-bulk-memory --enable-sign-ext --enable-nontrapping-float-to-int \
    --strip-debug --strip-producers --vacuum "${RAW_VAULT_BIN}" -o "${OPT_VAULT_BIN}"
else
  if [ -n "${CI:-}" ]; then
    echo "Error: CI環境では 'wasm-opt' (binaryen) が必須です。" >&2
    exit 1
  fi
  echo "Warning: 'wasm-opt' が見つかりません。未最適化Rawバイナリを検査対象とします。" >&2
  cp "${RAW_LITE_BIN}" "${OPT_LITE_BIN}"
  cp "${RAW_VAULT_BIN}" "${OPT_VAULT_BIN}"
fi

# ファイルサイズの取得関数。
get_file_size() {
  local file_path="$1"
  if [[ "${OSTYPE:-}" == "darwin"* ]]; then
    stat -f%z "${file_path}"
  else
    stat -c%s "${file_path}"
  fi
}

LITE_RAW_SIZE=$(get_file_size "${OPT_LITE_BIN}")
VAULT_RAW_SIZE=$(get_file_size "${OPT_VAULT_BIN}")

# Brotli圧縮サイズの取得。
LITE_WIRE_SIZE="N/A"
VAULT_WIRE_SIZE="N/A"
LITE_WIRE_STATUS="SKIP"
VAULT_WIRE_STATUS="SKIP"
if command -v brotli >/dev/null 2>&1; then
  brotli -q 11 -c "${OPT_LITE_BIN}" > "${OPT_LITE_BIN}.br"
  brotli -q 11 -c "${OPT_VAULT_BIN}" > "${OPT_VAULT_BIN}.br"
  LITE_WIRE_SIZE=$(get_file_size "${OPT_LITE_BIN}.br")
  VAULT_WIRE_SIZE=$(get_file_size "${OPT_VAULT_BIN}.br")

  LITE_WIRE_STATUS="PASS"
  if [ "${LITE_WIRE_SIZE}" -ge "${MAX_LITE_WIRE}" ]; then
    LITE_WIRE_STATUS="FAIL"
  fi

  VAULT_WIRE_STATUS="PASS"
  if [ "${VAULT_WIRE_SIZE}" -ge "${MAX_VAULT_WIRE}" ]; then
    VAULT_WIRE_STATUS="FAIL"
  fi
else
  if [ -n "${CI:-}" ]; then
    echo "Error: CI環境では 'brotli' が必須です。" >&2
    exit 1
  fi
  echo "Warning: 'brotli' が見つかりません。Wire容量ゲートの判定をスキップします。" >&2
fi

LITE_RAW_STATUS="PASS"
if [ "${LITE_RAW_SIZE}" -ge "${MAX_LITE_RAW}" ]; then
  LITE_RAW_STATUS="FAIL"
fi

VAULT_RAW_STATUS="PASS"
if [ "${VAULT_RAW_SIZE}" -ge "${MAX_VAULT_RAW}" ]; then
  VAULT_RAW_STATUS="FAIL"
fi

echo ""
echo "======================== Wasm Binary Size Report ========================"
printf "%-15s | %-10s | %-10s | %-6s | %-10s | %-10s | %-6s\n" \
  "Profile" "Raw Size" "Raw Limit" "Raw" "Wire Size" "Wire Limit" "Wire"
printf -- "-------------------------------------------------------------------------\n"
printf "%-15s | %8d B | %8d B | %-6s | %8s B | %8d B | %-6s\n" \
  "profile-lite" "${LITE_RAW_SIZE}" "${MAX_LITE_RAW}" "${LITE_RAW_STATUS}" \
  "${LITE_WIRE_SIZE}" "${MAX_LITE_WIRE}" "${LITE_WIRE_STATUS}"
printf "%-15s | %8d B | %8d B | %-6s | %8s B | %8d B | %-6s\n" \
  "profile-vault" "${VAULT_RAW_SIZE}" "${MAX_VAULT_RAW}" "${VAULT_RAW_STATUS}" \
  "${VAULT_WIRE_SIZE}" "${MAX_VAULT_WIRE}" "${VAULT_WIRE_STATUS}"
echo "========================================================================="
echo ""

# GitHub Actions Step Summary の出力。
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  {
    echo "### Wasm Binary Size Gate Results"
    echo ""
    echo "| Profile | Raw Size | Raw Limit | Raw Status | Wire (Brotli) | Wire Limit | Wire Status |"
    echo "| :--- | :--- | :--- | :--- | :--- | :--- | :--- |"
    echo "| **Lite / Auth** | ${LITE_RAW_SIZE} bytes | < ${MAX_LITE_RAW} bytes | ${LITE_RAW_STATUS} | ${LITE_WIRE_SIZE} bytes | < ${MAX_LITE_WIRE} bytes | ${LITE_WIRE_STATUS} |"
    echo "| **Full / Vault** | ${VAULT_RAW_SIZE} bytes | < ${MAX_VAULT_RAW} bytes | ${VAULT_RAW_STATUS} | ${VAULT_WIRE_SIZE} bytes | < ${MAX_VAULT_WIRE} bytes | ${VAULT_WIRE_STATUS} |"
    echo ""
  } >> "${GITHUB_STEP_SUMMARY}"
fi

# 失敗時の診断出力およびプロセス終了。
if [ "${LITE_RAW_STATUS}" = "FAIL" ] || [ "${VAULT_RAW_STATUS}" = "FAIL" ] || [ "${LITE_WIRE_STATUS}" = "FAIL" ] || [ "${VAULT_WIRE_STATUS}" = "FAIL" ]; then
  echo "Error: Wasmバイナリサイズが規定の上限値を超過しました。" >&2
  if command -v cargo-bloat >/dev/null 2>&1; then
    echo "==> Symbol breakdown via cargo-bloat:"
    cargo bloat --target wasm32-unknown-unknown --release -p fidelogic-wasm -n 20 || true
  fi
  exit 1
fi

echo "==> [SUCCESS] All Wasm size gate constraints satisfied."
