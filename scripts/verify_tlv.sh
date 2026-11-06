#!/usr/bin/env bash
# Charon / Aeneas 経由のTLVモデル抽出・証明・公理監査を一括実行するスクリプト。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

echo "==> [1/4] Extracting LLBC from Rust via Charon..."
mkdir -p target
charon cargo --preset aeneas \
  --start-from fidelogic_core::tlv::parse_tlv_header \
  --start-from fidelogic_core::tlv::validate_tlv_bounds \
  --start-from fidelogic_core::tlv::deserialize_header \
  --start-from fidelogic_core::tlv::serialize_header \
  --start-from fidelogic_core::tlv::is_known_tag \
  --start-from fidelogic_core::tlv::deserialize_slot_entry \
  --start-from fidelogic_core::tlv::deserialize_record \
  --start-from fidelogic_core::tlv::record_serialized_len \
  --dest-file "${REPO_ROOT}/target/fidelogic_core.llbc" \
  -- -p fidelogic-core

echo "==> [2/4] Generating Rocq theories via Aeneas..."
mkdir -p proofs/Theories
aeneas -backend rocq -dest proofs/Theories target/fidelogic_core.llbc

# Aeneas 生成ファイルのインポートを Dune 論理名空間へ正規化。
python3 -c '
path = "proofs/Theories/FidelogicCore.v"
with open(path, "r") as f:
    c = f.read()
c = c.replace("Require Import List.", "From Stdlib Require Import List.")
c = c.replace("Require Import Primitives.", "From Fidelogic.Aeneas Require Import Primitives.")
with open(path, "w") as f:
    f.write(c)
'

echo "==> [3/4] Building Rocq proofs via Dune..."
"${SCRIPT_DIR}/build_proofs.sh"

echo "==> [4/4] Auditing axioms for TLV soundness theorems..."
python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvSoundness \
  --theorem tlv_parse_tlv_header_underflow \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvSoundness \
  --theorem tlv_validate_tlv_bounds_implies_header_some \
  --allow-aeneas-axioms

echo "==> [SUCCESS] All TLV extraction, proofs, and axiom audits passed cleanly."
