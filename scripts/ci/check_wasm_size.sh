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
  --features profile-lite \
  --target-dir "${TARGET_DIR}/lite_build"

RAW_LITE_BIN="${TARGET_DIR}/lite_build/wasm32-unknown-unknown/release/fidelogic_wasm.wasm"
OPT_LITE_BIN="${TARGET_DIR}/fidelogic_lite_opt.wasm"

echo "==> [2/4] Building fidelogic-wasm (profile-vault)..."
cargo build -p fidelogic-wasm \
  --target wasm32-unknown-unknown \
  --release \
  --no-default-features \
  --features profile-vault,std \
  --target-dir "${TARGET_DIR}/vault_build"

RAW_VAULT_BIN="${TARGET_DIR}/vault_build/wasm32-unknown-unknown/release/fidelogic_wasm.wasm"
OPT_VAULT_BIN="${TARGET_DIR}/fidelogic_vault_opt.wasm"

# 最適化 (`wasm-opt`) の適用。
if command -v wasm-opt >/dev/null 2>&1; then
  echo "==> Applying wasm-opt -Oz to Lite profile..."
  wasm-opt -Oz --strip-debug --strip-producers --vacuum "${RAW_LITE_BIN}" -o "${OPT_LITE_BIN}"

  echo "==> Applying wasm-opt -Oz to Vault profile..."
  wasm-opt -Oz --strip-debug --strip-producers --vacuum "${RAW_VAULT_BIN}" -o "${OPT_VAULT_BIN}"
else
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
if command -v brotli >/dev/null 2>&1; then
  brotli -q 11 -c "${OPT_LITE_BIN}" > "${OPT_LITE_BIN}.br"
  brotli -q 11 -c "${OPT_VAULT_BIN}" > "${OPT_VAULT_BIN}.br"
  LITE_WIRE_SIZE=$(get_file_size "${OPT_LITE_BIN}.br")
  VAULT_WIRE_SIZE=$(get_file_size "${OPT_VAULT_BIN}.br")
fi

echo ""
echo "================ Wasm Binary Size Report ================"
printf "%-15s | %-12s | %-12s | %-10s\n" "Profile" "Raw Size" "Raw Limit" "Result"
printf -- "---------------------------------------------------------\n"

LITE_STATUS="PASS"
if [ "${LITE_RAW_SIZE}" -gt "${MAX_LITE_RAW}" ]; then
  LITE_STATUS="FAIL"
fi
printf "%-15s | %10d B | %10d B | %-10s\n" "profile-lite" "${LITE_RAW_SIZE}" "${MAX_LITE_RAW}" "${LITE_STATUS}"

VAULT_STATUS="PASS"
if [ "${VAULT_RAW_SIZE}" -gt "${MAX_VAULT_RAW}" ]; then
  VAULT_STATUS="FAIL"
fi
printf "%-15s | %10d B | %10d B | %-10s\n" "profile-vault" "${VAULT_RAW_SIZE}" "${MAX_VAULT_RAW}" "${VAULT_STATUS}"
echo "========================================================="
echo "Wire Size (Brotli): Lite=${LITE_WIRE_SIZE} B, Vault=${VAULT_WIRE_SIZE} B"
echo ""

# GitHub Actions Step Summary の出力。
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  {
    echo "### Wasm Binary Size Gate Results"
    echo ""
    echo "| Profile | Raw Size | Limit | Wire (Brotli) | Status |"
    echo "| :--- | :--- | :--- | :--- | :--- |"
    echo "| **Lite / Auth** | ${LITE_RAW_SIZE} bytes | < ${MAX_LITE_RAW} bytes | ${LITE_WIRE_SIZE} bytes | ${LITE_STATUS} |"
    echo "| **Full / Vault** | ${VAULT_RAW_SIZE} bytes | < ${MAX_VAULT_RAW} bytes | ${VAULT_WIRE_SIZE} bytes | ${VAULT_STATUS} |"
    echo ""
  } >> "${GITHUB_STEP_SUMMARY}"
fi

# 失敗時の診断出力およびプロセス終了。
if [ "${LITE_STATUS}" = "FAIL" ] || [ "${VAULT_STATUS}" = "FAIL" ]; then
  echo "Error: Wasmバイナリサイズが規定の上限値を超過しました。" >&2
  if command -v cargo-bloat >/dev/null 2>&1; then
    echo "==> Symbol breakdown via cargo-bloat:"
    cargo bloat --target wasm32-unknown-unknown --release -p fidelogic-wasm -n 20 || true
  fi
  exit 1
fi

echo "==> [SUCCESS] All Wasm size gate constraints satisfied."
