#!/usr/bin/env bash
# Charon / Aeneas 経由のTLVモデル抽出・証明・公理監査を一括実行するスクリプト。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

echo "==> [1/4] Extracting LLBC from Rust via Charon..."
mkdir -p target

# 【Charon/Aeneas 抽出対象選定および Coq手書きモデル連携の根拠】
# fidelogic_core::tlv::deserialize および serialize は、
# ループ内の早期リターン・ブレイク(? 演算子による Result エラー伝播)を含んでおり、
# 現行の Aeneas loop translation において、
# "Returns inside of nested loops are not supported yet", "Breaks to outer loops are not supported yet"
# として関数本体の抽出がスキップ(opaque宣言化)されます。
#
# そのため、トップレベルのVault全体デシリアライズ処理(deserialize)は、
# Aeneas自動抽出の基本プリミティブ(deserialize_header, deserialize_slot_entry, deserialize_record, ...)
# を結合する純粋関数型モデルとして、proofs/Theories/TlvTotality.v に、
# 構造帰納モデル(tlv_deserialize_slots, tlv_deserialize_records, tlv_deserialize)
# として形式化し、Rust側の saturating_mul 境界検査(core_num_Usize_saturating_mul)と厳密に一致させています。

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

echo "==> [4/4] Auditing axioms for TLV soundness and totality theorems..."
python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvSoundness \
  --theorem tlv_parse_tlv_header_underflow \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvSoundness \
  --theorem tlv_validate_tlv_bounds_implies_header_some \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvTotality \
  --theorem tlv_deserialize_header_underflow \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvTotality \
  --theorem tlv_deserialize_header_totality \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvTotality \
  --theorem tlv_deserialize_record_header_underflow \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvTotality \
  --theorem tlv_deserialize_record_underflow \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvTotality \
  --theorem tlv_deserialize_record_bounds_violation \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvTotality \
  --theorem tlv_deserialize_slots_totality \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvTotality \
  --theorem tlv_deserialize_records_totality \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvTotality \
  --theorem tlv_deserialize_totality \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_record_roundtrip_entry_minimal \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_record_roundtrip_known \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_record_roundtrip_unknown_minimal \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_record_roundtrip_unknown \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_header_roundtrip \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_header_roundtrip_sound \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_slot_roundtrip \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_slots_roundtrip \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_record_chain_roundtrip \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_records_roundtrip \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_vault_roundtrip \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_unknown_tag_structure_preservation \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_unknown_tag_structure_preservation_minimal \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_records_preserve_unknown_fields \
  --allow-aeneas-axioms

python3 "${SCRIPT_DIR}/audit_axioms.py" \
  --module Fidelogic.Theories.TlvRoundtrip \
  --theorem tlv_vault_preserve_unknown_fields \
  --allow-aeneas-axioms

echo "==> [SUCCESS] All TLV extraction, proofs, and axiom audits passed cleanly."
