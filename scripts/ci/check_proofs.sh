#!/usr/bin/env bash
# Rocq定理の形式検証ビルドおよび全対象補題の公理監査を一括実行するCIスクリプト。
# `Admitted` や未承認公理の混入を機械的に検出し、失敗時に非ゼロ終了コードを返す。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
cd "${REPO_ROOT}"

echo "==> Building all Rocq proof theories via Dune..."
"${REPO_ROOT}/scripts/build_proofs.sh"

AUDIT_SCRIPT="${REPO_ROOT}/scripts/audit_axioms.py"
if [ ! -f "${AUDIT_SCRIPT}" ]; then
  echo "Error: audit_axioms.py が存在しません。" >&2
  exit 1
fi

echo "==> Auditing axioms for sanity theorem..."
python3 "${AUDIT_SCRIPT}" \
  --module Fidelogic.Sanity \
  --theorem sanity_add_comm

echo "==> Auditing axioms for TLV soundness theorems..."
python3 "${AUDIT_SCRIPT}" \
  --module Fidelogic.Theories.TlvSoundness \
  --theorem tlv_parse_tlv_header_underflow \
  --allow-aeneas-axioms

python3 "${AUDIT_SCRIPT}" \
  --module Fidelogic.Theories.TlvSoundness \
  --theorem tlv_validate_tlv_bounds_implies_header_some \
  --allow-aeneas-axioms

echo "==> [SUCCESS] All Rocq proofs and axiom audits passed cleanly without Admitted."
