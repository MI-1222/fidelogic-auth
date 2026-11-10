#!/usr/bin/env bash
# Fidelogic 統合ドキュメント生成オーケストレータースクリプト。
# Rust API ドキュメント (cargo doc) および Rocq 形式検証証明 (Alectryon) を一括生成し、
# 統合ポータル (public/) を構築する。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

TARGET="${1:-all}"

case "${TARGET}" in
  --portal-only|portal)
    "${SCRIPT_DIR}/build_portal.sh"
    ;;
  --rust-only|rust)
    "${SCRIPT_DIR}/build_rust_docs.sh"
    "${SCRIPT_DIR}/build_portal.sh"
    ;;
  --proofs-only|proofs)
    "${SCRIPT_DIR}/build_proofs_alectryon.sh"
    "${SCRIPT_DIR}/build_portal.sh"
    ;;
  all|*)
    echo "==> [1/3] Building Rust API documentation..."
    if command -v cargo >/dev/null 2>&1; then
      "${SCRIPT_DIR}/build_rust_docs.sh"
    else
      echo "Notice: cargo が検出されないため、Rust API ドキュメント生成をスキップします。"
    fi

    echo "==> [2/3] Building Rocq proof documentation (Alectryon)..."
    if command -v alectryon >/dev/null 2>&1 || [ -f "${REPO_ROOT}/.local/alectryon/alectryon.py" ]; then
      "${SCRIPT_DIR}/build_proofs_alectryon.sh"
    else
      echo "Notice: Alectryon が検出されないため、Rocq 証明ドキュメント生成をスキップします。"
    fi

    echo "==> [3/3] Generating integrated top portal..."
    "${SCRIPT_DIR}/build_portal.sh"
    echo "==> [SUCCESS] 全ドキュメントの生成が完了しました: ${REPO_ROOT}/public"
    ;;
esac
