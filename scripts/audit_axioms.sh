#!/usr/bin/env bash
# Fidelogic Rocq定理の公理・健全性監査スクリプト。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

# 1. 先にビルドスクリプトを呼び出して .vo 成果物を最新化
"${SCRIPT_DIR}/build_proofs.sh"

# 2. 監査用スクリプトの解決
AUDIT_SCRIPT=""
if [ -f "${SCRIPT_DIR}/audit_axioms.py" ]; then
  AUDIT_SCRIPT="${SCRIPT_DIR}/audit_axioms.py"
else
  echo "Error: audit_axioms.py が見つかりません。scripts/audit_axioms.py を配置してください。" >&2
  exit 1
fi

# 3. Python環境チェックと監査実行
if ! command -v python3 >/dev/null 2>&1; then
  echo "Error: 'python3' が見つかりません。" >&2
  exit 1
fi

echo "==> Auditing axioms and assumptions..."
python3 "${AUDIT_SCRIPT}" "$@"
