#!/usr/bin/env bash
# Fidelogic Rocq形式検証モデルのDuneビルド実行スクリプト。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

# 1. opam環境の読み込み(既に環境変数がセットされていない場合のみ)
if [ -z "${OPAM_SWITCH_PREFIX:-}" ] && command -v opam >/dev/null 2>&1; then
  eval "$(opam env)"
fi

# 2. macOS用 Rocq-Platform アプリケーションの自動検出(フォールバック: macOS環境のみ実行)
if [[ "${OSTYPE:-}" == "darwin"* ]]; then
  if ! command -v dune >/dev/null 2>&1 || ! command -v rocq >/dev/null 2>&1; then
    if [ -z "${ROCQ_PLATFORM_DIR:-}" ] && [ -d /Applications ]; then
      LATEST_APP=$(find /Applications -maxdepth 1 -name "Rocq-Platform*.app" 2>/dev/null | sort -V | tail -n 1 || true)
      if [ -n "${LATEST_APP}" ]; then
        ROCQ_PLATFORM_DIR="${LATEST_APP}/Contents/Resources"
      fi
    fi

    if [ -n "${ROCQ_PLATFORM_DIR:-}" ] && [ -d "${ROCQ_PLATFORM_DIR}" ]; then
      export PATH="${ROCQ_PLATFORM_DIR}/bin:${PATH}"
      export ROCQLIB="${ROCQ_PLATFORM_DIR}/lib/coq"
      export COQLIB="${ROCQ_PLATFORM_DIR}/lib/coq"
      export OCAMLFIND_CONF="${ROCQ_PLATFORM_DIR}/lib/findlib.conf"
      export OCAMLPATH="${ROCQ_PLATFORM_DIR}/lib"
    fi
  fi
fi

# 3. 実行依存コマンドの検証
if ! command -v dune >/dev/null 2>&1; then
  echo "Error: 'dune' が見つかりません。opam 環境を初期化するか、Rocq-Platform を導入してください。" >&2
  exit 1
fi

echo "==> Building Rocq proofs via Dune..."
dune build "$@"
