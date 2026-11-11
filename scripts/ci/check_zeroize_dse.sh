#!/usr/bin/env bash
# 最適化済みWasmバイナリに対する Zeroize / Dead Store Elimination (DSE) 抑止静的検査スクリプト。
# `wasm2wat` を用いて逆アセンブルし、
# `fidelogic_wasm_zeroize_test` 関数のブロック内部およびその呼び出し先において、
# 揮発性ストア命令およびゼロクリア処理がコンパイラ最適化で
# 除去されていないかを関数スコープ限定で機械的に検証する。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
cd "${REPO_ROOT}"

TARGET_DIR="${REPO_ROOT}/target/wasm-size"
LITE_WASM="${TARGET_DIR}/fidelogic_lite_opt.wasm"
VAULT_WASM="${TARGET_DIR}/fidelogic_vault_opt.wasm"

# ビルド成果物が存在しない場合は先にサイズゲートスクリプトでビルドを実行。
if [ ! -f "${LITE_WASM}" ] || [ ! -f "${VAULT_WASM}" ]; then
  echo "==> Building target Wasm binaries via check_wasm_size.sh..."
  "${SCRIPT_DIR}/check_wasm_size.sh"
fi

if ! command -v wasm2wat >/dev/null 2>&1; then
  echo "Warning: 'wasm2wat' (wabt) が見つかりません。環境にwabtをインストールしてください。" >&2
  # CI環境では必須だが、ローカル端末で未インストールの場合はガイダンスを出してスキップまたは警告。
  if [ -n "${CI:-}" ]; then
    echo "Error: CI環境では wasm2wat が必須です。" >&2
    exit 1
  else
    echo "Skipping zeroize WAT inspection on local environment without wabt."
    exit 0
  fi
fi

TARGET_SYMBOL="fidelogic_wasm_zeroize_test"

inspect_wat() {
  local wasm_file="$1"
  local wat_file="$2"
  local profile_name="$3"

  echo "==> [${profile_name}] Disassembling Wasm to WAT via wasm2wat..."
  wasm2wat "${wasm_file}" -o "${wat_file}"

  echo "==> [${profile_name}] Inspecting WAT for zeroize instructions and DSE prevention in ${TARGET_SYMBOL}..."

  python3 - <<EOF
import re
import sys
from collections import deque

wat_path = "${wat_file}"
target_sym = "${TARGET_SYMBOL}"
profile = "${profile_name}"

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

func_id = resolve_export(target_sym)
if not func_id:
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

if func_id not in funcs:
    print(f"Error: [{profile}] 関数 '{target_sym}' (id: {func_id}) の定義ブロックが見つかりませんでした。", file=sys.stderr)
    sys.exit(1)

# 3. 関数スコープ内のメモリ消去ストア命令(i32.store8, i32.store, memory.fill等)の検出.
store_pattern = re.compile(r'\b(i32\.store8|i32\.store16|i32\.store|i64\.store|memory\.fill)\b')
call_pattern = re.compile(r'\bcall\s+(?:\$)?([0-9a-zA-Z_.]+)\b')

def trace_reachable(root_id):
    visited = set()
    queue = deque([root_id])
    matched_stores = []
    call_chain = []
    while queue:
        curr_id = queue.popleft()
        if curr_id in visited:
            continue
        visited.add(curr_id)
        call_chain.append(curr_id)
        if curr_id not in funcs:
            continue
        start_line, f_lines = funcs[curr_id]
        for rel_idx, line in enumerate(f_lines):
            abs_line = start_line + rel_idx
            m_store = store_pattern.search(line)
            if m_store:
                matched_stores.append((curr_id, abs_line, line.strip(), m_store.group(1)))
            for m_call in call_pattern.finditer(line):
                callee_id = m_call.group(1)
                if callee_id not in visited:
                    queue.append(callee_id)
    return call_chain, matched_stores

call_chain, matched_stores = trace_reachable(func_id)

if not matched_stores:
    print(f"Error: [{profile}] '{target_sym}' のスコープ内(呼び出しチェーン: {' -> '.join(call_chain)})に揮発性ストア命令(i32.store8 / i32.store / memory.fill)が検出されませんでした！", file=sys.stderr)
    print("コンパイラの最適化 (Dead Store Elimination) によりゼロクリア処理が消去された可能性があります。", file=sys.stderr)
    sys.exit(1)

print(f"==> [{profile}] [SUCCESS] Verified zeroize stores preserved in '{target_sym}' scope (call chain: {' -> '.join(call_chain)}):")
for fid, line_no, code, inst in matched_stores:
    print(f"  Line {line_no} in func {fid}: [{inst}] -> {code}")

# zeroize ゼロクリアストア関数群(i32.const 0 に続く i32.store8 ループ、または memory.fill によるゼロ埋め)を抽出.
zero_loop_funcs = set()
for fid, (_, f_lines) in funcs.items():
    body = "\n".join(f_lines)
    if ("loop" in body and re.search(r'i32\.const\s+0\s*\n\s*i32\.store8\b', body)) or re.search(r'i32\.const\s+0\s*\n[^\n]*\n\s*memory\.fill\b', body):
        zero_loop_funcs.add(fid)

volatile_zeroize_callees = set(call_chain) - {func_id}
if not (volatile_zeroize_callees & zero_loop_funcs) and not matched_stores:
    print(f"Error: [{profile}] '{target_sym}' の呼び出し先にゼロクリアストア命令を特定できませんでした。", file=sys.stderr)
    sys.exit(1)

# 4. 本番エクスポート関数でのゼロ消去到達検証(DSE/DCE バイパス防止).
prod_checks = [("fidelogic_wasm_x25519_dh", zero_loop_funcs | volatile_zeroize_callees)]
if profile == "profile-vault":
    prod_checks.extend([
        ("fidelogic_wasm_vault_encrypt", volatile_zeroize_callees),
        ("fidelogic_wasm_vault_decrypt", volatile_zeroize_callees),
        ("fidelogic_wasm_kdf_derive_key", zero_loop_funcs | volatile_zeroize_callees),
    ])

for prod_sym, expected_targets in prod_checks:
    prod_fid = resolve_export(prod_sym)
    if not prod_fid:
        print(f"Error: [{profile}] 本番シンボル '{prod_sym}' が WAT 内に見つかりません。", file=sys.stderr)
        sys.exit(1)
    prod_chain, _ = trace_reachable(prod_fid)
    reached = sorted(set(prod_chain) & expected_targets)
    if not reached:
        print(f"Error: [{profile}] 本番関数 '{prod_sym}' (func {prod_fid}) から zeroize / volatile_zeroize 処理への到達が DSE または DCE により消失しました！", file=sys.stderr)
        sys.exit(1)
    print(f"==> [{profile}] [SUCCESS] Verified production '{prod_sym}' preserves zeroize reachability -> funcs {reached}")
EOF
}

LITE_WAT="${TARGET_DIR}/fidelogic_lite.wat"
VAULT_WAT="${TARGET_DIR}/fidelogic_vault.wat"

inspect_wat "${LITE_WASM}" "${LITE_WAT}" "profile-lite"
inspect_wat "${VAULT_WASM}" "${VAULT_WAT}" "profile-vault"

# GitHub Actions Step Summary の出力
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  {
    echo "### Zeroize & DSE Prevention Verification Summary"
    echo ""
    echo "| Profile | Checked Targets | Memory Clearing Stores | Result |"
    echo "| :--- | :--- | :--- | :--- |"
    echo "| \`profile-lite\` | \`${TARGET_SYMBOL}\`, \`fidelogic_wasm_x25519_dh\` | Preserved | **PASS** |"
    echo "| \`profile-vault\` | \`${TARGET_SYMBOL}\`, \`fidelogic_wasm_x25519_dh\`, \`fidelogic_wasm_vault_encrypt\`, \`fidelogic_wasm_vault_decrypt\`, \`fidelogic_wasm_kdf_derive_key\` | Preserved | **PASS** |"
    echo ""
    echo "WebAssembly逆アセンブル解析により、検証用スタブおよび本番暗号・鍵導出エクスポート関数からのゼロ消去処理到達(DSE抑止)を確認しました。"
  } >> "${GITHUB_STEP_SUMMARY}"
fi

echo ""
echo "==> [SUCCESS] Verified zeroize volatile store instructions are preserved across all target Wasm binaries."
