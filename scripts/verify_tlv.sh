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

# Aeneas 生成ファイルのインポートを Dune 論理名空間へ正規化し、後方互換エイリアスを注入。
python3 -c '
path = "proofs/Theories/FidelogicCore.v"
with open(path, "r") as f:
    c = f.read()
c = c.replace("Require Import List.", "From Stdlib Require Import List.")
c = c.replace("Require Import Primitives.", "From Fidelogic.Aeneas Require Import Primitives.")
aliases = """
(** 後方互換用エイリアス (形式検証証明資産との意味論的互換性を維持)。 *)
Notation tlv_VaultError_t := error_TlvParseError_t.
Notation Tlv_VaultError_UnexpectedEof := Error_TlvParseError_UnexpectedEof.
Notation Tlv_VaultError_InvalidMagic := Error_TlvParseError_InvalidMagic.
Notation Tlv_VaultError_InvalidLength := Error_TlvParseError_InvalidLength.
Notation Tlv_VaultError_InvalidFormat := Error_TlvParseError_InvalidFormat.
Notation Tlv_VaultError_UnsupportedVersion := Error_TlvParseError_UnsupportedVersion.
Notation Tlv_VaultError_UnsupportedSuite := Error_TlvParseError_UnsupportedSuite.
Notation alloc_vec_Vec_Insts_CoreConvertFromShared0Slice_from := alloc_slice_Slice_to_vec.
Definition tlv_KekSlotEntry_wrapped_dek_len (slot : tlv_KekSlotEntry_t) : u16 :=
  u16_of_Z (Z.of_nat (length (alloc_vec_Vec_to_list slot.(tlv_KekSlotEntry_wrapped_dek)))).
"""
c = c.replace("End FidelogicCore.", aliases + "\nEnd FidelogicCore.")
with open(path, "w") as f:
    f.write(c)
'

echo "==> [3/4] Building Rocq proofs via Dune..."
"${SCRIPT_DIR}/build_proofs.sh"

echo "==> [4/4] Auditing all formal proof theorems against kernel axioms..."
python3 "${SCRIPT_DIR}/audit_axioms.py" --manifest "${REPO_ROOT}/proofs/audited_theorems.json"

echo "==> [SUCCESS] All TLV extraction, proofs, and axiom audits passed cleanly."
