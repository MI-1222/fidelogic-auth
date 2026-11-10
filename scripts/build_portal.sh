#!/usr/bin/env bash
# Fidelogic 統合トップポータル (public/index.html) 配置スクリプト。
# .github/pages/index.html を public/index.html にコピー配置する。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

PUBLIC_DIR="${REPO_ROOT}/public"
mkdir -p "${PUBLIC_DIR}"

TEMPLATE_FILE="${REPO_ROOT}/.github/pages/index.html"
if [ ! -f "${TEMPLATE_FILE}" ]; then
  echo "Error: ${TEMPLATE_FILE} が見つかりません。" >&2
  exit 1
fi

echo "==> Deploying top portal from ${TEMPLATE_FILE} to ${PUBLIC_DIR}/index.html..."
cp "${TEMPLATE_FILE}" "${PUBLIC_DIR}/index.html"

echo "==> [SUCCESS] 統合トップポータルが配置されました: ${PUBLIC_DIR}/index.html"
