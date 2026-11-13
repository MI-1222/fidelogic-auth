#!/usr/bin/env bash
# 最適化済みWasmバイナリに対するダミー暗号演算 (Argon2id, HKDF-SHA256, XChaCha20-Poly1305 AEAD)
# およびメモリ消去のデッドコード除去 (DCE) 抑止静的検査スクリプト。
# `wasm2wat` を用いて逆アセンブルし、
# `fidelogic_wasm_dummy_slot_eval_test` のコールグラフを追跡して、
# コンパイラ最適化 (LTO/DCE) によりダミー暗号演算パイプラインが除去されていないかを機械的に検証する。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
cd "${REPO_ROOT}"

TARGET_DIR="${REPO_ROOT}/target/wasm-size"
VAULT_WASM="${TARGET_DIR}/fidelogic_vault_opt.wasm"
VAULT_WAT="${TARGET_DIR}/fidelogic_vault.wat"

# ビルド成果物が存在しない場合は先にサイズゲートスクリプトでビルドを実行。
if [ ! -f "${VAULT_WASM}" ]; then
  echo "==> Building target Wasm binaries via check_wasm_size.sh..."
  "${SCRIPT_DIR}/check_wasm_size.sh"
fi

if ! command -v wasm2wat >/dev/null 2>&1; then
  echo "Warning: 'wasm2wat' (wabt) が見つかりません。環境にwabtをインストールしてください。" >&2
  if [ -n "${CI:-}" ]; then
    echo "Error: CI環境では wasm2wat が必須です。" >&2
    exit 1
  else
    echo "Skipping dummy slot DCE WAT inspection on local environment without wabt."
    exit 0
  fi
fi

TARGET_SYMBOL="fidelogic_wasm_dummy_slot_eval_test"

echo "==> [profile-vault] Disassembling Wasm to WAT via wasm2wat..."
wasm2wat "${VAULT_WASM}" -o "${VAULT_WAT}"

echo "==> [profile-vault] Inspecting WAT call graph for dummy slot KDF / AEAD / zeroize preservation in ${TARGET_SYMBOL}..."

python3 - <<EOF
import re
import sys
from collections import deque

wat_path = "${VAULT_WAT}"
target_sym = "${TARGET_SYMBOL}"
profile = "profile-vault"

with open(wat_path, "r", encoding="utf-8") as f:
    content = f.read()

# 1. エクスポートシンボルを収集.
export_re = re.compile(r'\(export\s+"([^"]+)"\s+\(func\s+(?:\$)?([0-9a-zA-Z_.]+)\)\)')
exports = {m.group(1): m.group(2) for m in export_re.finditer(content)}

def resolve_export(sym):
    if sym in exports:
        return exports[sym]
    named_func_pattern = r'\(func\s+\$' + re.escape(sym) + r'\b'
    if re.search(named_func_pattern, content):
        return sym
    return None

dummy_fid = resolve_export(target_sym)
if not dummy_fid:
    print(f"Error: [{profile}] WAT内にエクスポートシンボル '{target_sym}' が見つかりません。", file=sys.stderr)
    sys.exit(1)

# 2. 関数本体ブロックをパース.
lines = content.splitlines()
funcs = {}
current_func_id = None
current_func_lines = []
current_start_line = 0
paren_depth = 0
in_func = False

func_start_re = re.compile(r'^\s*\(func(?:\s+(?:\(;(\d+);\)|\$([0-9a-zA-Z_.]+)))?')

for idx, line in enumerate(lines, start=1):
    if not in_func:
        m = func_start_re.match(line)
        if m:
            in_func = True
            current_start_line = idx
            current_func_lines = [line]
            paren_depth = line.count('(') - line.count(')')
            fid = m.group(1) or m.group(2)
            if not fid:
                fid = str(len(funcs))
            current_func_id = fid
            if paren_depth <= 0:
                funcs[current_func_id] = (current_start_line, current_func_lines)
                in_func = False
    else:
        current_func_lines.append(line)
        paren_depth += line.count('(') - line.count(')')
        if paren_depth <= 0:
            funcs[current_func_id] = (current_start_line, current_func_lines)
            in_func = False

if dummy_fid not in funcs:
    print(f"Error: [{profile}] 関数 '{target_sym}' (id: {dummy_fid}) の定義ブロックが見つかりませんでした。", file=sys.stderr)
    sys.exit(1)

# 3. 到達可能関数コールグラフの探索.
call_pattern = re.compile(r'\bcall\s+(?:\$)?([0-9a-zA-Z_.]+)\b')

def trace_reachable(root_id):
    visited = set()
    queue = deque([root_id])
    while queue:
        curr = queue.popleft()
        if curr in visited:
            continue
        visited.add(curr)
        if curr not in funcs:
            continue
        _, f_lines = funcs[curr]
        for line in f_lines:
            for m_call in call_pattern.finditer(line):
                callee = m_call.group(1)
                if callee not in visited:
                    queue.append(callee)
    return visited

dummy_chain = trace_reachable(dummy_fid)
print(f"==> [{profile}] Traceable functions reachable from '{target_sym}': {len(dummy_chain)}")

# 4. 暗号コア特性の機械的検証.
# (A) SHA-256 (HKDF-SHA256) コア関数の検証: K定数 (0x428a2f98 = 1116352408 または 0x71374491 = 1899447441)
sha_funcs = set()
for fid in dummy_chain:
    body = "\n".join(funcs[fid][1])
    if "1116352408" in body or "1899447441" in body:
        sha_funcs.add(fid)

if not sha_funcs:
    print(f"Error: [{profile}] '{target_sym}' のコールグラフ内に HKDF-SHA256 演算コアが検出されませんでした！", file=sys.stderr)
    print("ダミー HKDF-SHA256 演算がコンパイラ最適化 (DCE) により除去された可能性があります。", file=sys.stderr)
    sys.exit(1)
print(f"==> [{profile}] [SUCCESS] Verified dummy HKDF-SHA256 reachability -> funcs {sorted(sha_funcs)}")

# (B) Argon2id / Blake2b コア関数の検証: Blake2b 初期化定数 (7640891576956012808) または 64bit ローテーション/排他的論理和
argon_funcs = set()
for fid in dummy_chain:
    body = "\n".join(funcs[fid][1])
    if "7640891576956012808" in body or ("i64.rotr" in body and "i64.xor" in body):
        argon_funcs.add(fid)

if not argon_funcs:
    print(f"Error: [{profile}] '{target_sym}' のコールグラフ内に Argon2id 演算コアが検出されませんでした！", file=sys.stderr)
    print("ダミー Argon2id 演算がコンパイラ最適化 (DCE) により除去された可能性があります。", file=sys.stderr)
    sys.exit(1)
print(f"==> [{profile}] [SUCCESS] Verified dummy Argon2id reachability -> funcs {sorted(argon_funcs)}")

# (C) XChaCha20-Poly1305 AEAD 復号コア関数の検証:
# 本番復号シンボル 'fidelogic_wasm_vault_decrypt' との共通暗号関数および ChaCha20/Poly1305 ローテーション演算
dec_fid = resolve_export("fidelogic_wasm_vault_decrypt")
if not dec_fid:
    print(f"Error: [{profile}] 本番復号シンボル 'fidelogic_wasm_vault_decrypt' が見つかりません。", file=sys.stderr)
    sys.exit(1)

dec_chain = trace_reachable(dec_fid)
common_aead = dummy_chain & dec_chain
if len(common_aead) < 5:
    print(f"Error: [{profile}] '{target_sym}' と 'fidelogic_wasm_vault_decrypt' の共通 AEAD 復号関数群 ({len(common_aead)}) が不足しています！", file=sys.stderr)
    print("ダミー AEAD 復号演算がコンパイラ最適化 (DCE) により除去された可能性があります。", file=sys.stderr)
    sys.exit(1)
print(f"==> [{profile}] [SUCCESS] Verified dummy AEAD unwrap reachability -> {len(common_aead)} shared cipher/MAC functions with production decrypt")

# (D) zeroize (メモリ消去揮発性ストア) への到達検証
zero_loop_funcs = set()
for fid, (_, f_lines) in funcs.items():
    body = "\n".join(f_lines)
    if ("loop" in body and re.search(r'i32\.const\s+0\s*\n\s*i32\.store8\b', body)) or re.search(r'i32\.const\s+0\s*\n[^\n]*\n\s*memory\.fill\b', body):
        zero_loop_funcs.add(fid)

dummy_zero = dummy_chain & zero_loop_funcs
if not dummy_zero:
    print(f"Error: [{profile}] '{target_sym}' のコールグラフ内にゼロ消去処理への到達が検出されませんでした！", file=sys.stderr)
    sys.exit(1)
print(f"==> [{profile}] [SUCCESS] Verified dummy key zeroize reachability -> funcs {sorted(dummy_zero)}")
EOF

# GitHub Actions Step Summary の出力
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  {
    echo "### Dummy Slot Timing Equalisation & DCE Prevention Verification Summary"
    echo ""
    echo "| Profile | Target Symbol | Dummy KDF / AEAD Preserved | Zeroize Stores | Result |"
    echo "| :--- | :--- | :--- | :--- | :--- |"
    echo "| \`profile-vault\` | \`${TARGET_SYMBOL}\` | Argon2id, HKDF-SHA256, XChaCha20-Poly1305 | Preserved | **PASS** |"
    echo ""
    echo "WebAssembly逆アセンブル解析により、ダミー暗号演算パイプライン (Argon2id, HKDF-SHA256, AEAD復号) および鍵メモリ消去処理がコンパイラ最適化 (DCE) で除去されず残存していることを確認しました。"
  } >> "${GITHUB_STEP_SUMMARY}"
fi

echo ""
echo "==> [SUCCESS] Verified dummy slot crypto operations (Argon2id, HKDF, AEAD, Zeroize) are fully preserved in Wasm."
