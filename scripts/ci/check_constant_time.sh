#!/usr/bin/env bash
# 最適化済みWasmバイナリに対する定数時間暗号照合ブロックの静的検査スクリプト。
# `wasm2wat` を用いて逆アセンブルし、暗号照合関数内部に条件分岐命令(`br_if`, `if`, `br_table`)が
# 注入されていないかを機械的・静的に検証する。
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
  if [ -n "${CI:-}" ]; then
    echo "Error: CI環境では wasm2wat が必須です。" >&2
    exit 1
  else
    echo "Skipping constant-time WAT inspection on local environment without wabt."
    exit 0
  fi
fi

TARGET_SYMBOL="fidelogic_wasm_constant_time_eq_32"

inspect_wat() {
  local wasm_file="$1"
  local wat_file="$2"
  local profile_name="$3"

  echo "==> [${profile_name}] Disassembling Wasm to WAT via wasm2wat..."
  wasm2wat "${wasm_file}" -o "${wat_file}"

  echo "==> [${profile_name}] Inspecting WAT call graphs for constant-time properties..."

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

ct_func_id = resolve_export(target_sym)
if not ct_func_id:
    print(f"Error: [{profile}] WAT内にエクスポートシンボル '{target_sym}' が見つかりません。", file=sys.stderr)
    sys.exit(1)

dh_func_id = resolve_export("fidelogic_wasm_x25519_dh")
if not dh_func_id:
    print(f"Error: [{profile}] WAT内にエクスポートシンボル 'fidelogic_wasm_x25519_dh' が見つかりません。", file=sys.stderr)
    sys.exit(1)

dec_func_id = None
if profile == "profile-vault":
    dec_func_id = resolve_export("fidelogic_wasm_vault_decrypt")
    if not dec_func_id:
        print(f"Error: [{profile}] WAT内にエクスポートシンボル 'fidelogic_wasm_vault_decrypt' が見つかりません。", file=sys.stderr)
        sys.exit(1)

# 2. 全関数の本体ブロックをパース.
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

call_pattern = re.compile(r'\bcall\s+(?:\$)?([0-9a-zA-Z_.]+)\b')
branch_pattern = re.compile(r'\b(br_if|if|br_table)\b')

def collect_reachable(root_id):
    visited = set()
    queue = deque([root_id])
    order = []
    while queue:
        curr = queue.popleft()
        if curr in visited:
            continue
        visited.add(curr)
        order.append(curr)
        if curr not in funcs:
            continue
        _, f_lines = funcs[curr]
        for line in f_lines:
            for m_call in call_pattern.finditer(line):
                callee = m_call.group(1)
                if callee not in visited:
                    queue.append(callee)
    return order

# 3. fidelogic_wasm_constant_time_eq_32 とその全呼び出し先の完全無分岐検証.
ct_chain = collect_reachable(ct_func_id)
if ct_func_id not in funcs:
    print(f"Error: [{profile}] 関数 '{target_sym}' (id: {ct_func_id}) の定義ブロックを抽出できませんでした。", file=sys.stderr)
    sys.exit(1)

violations = []
for fid in ct_chain:
    if fid not in funcs:
        continue
    start_line, f_lines = funcs[fid]
    for rel_idx, line in enumerate(f_lines):
        m = branch_pattern.search(line)
        if m:
            violations.append((fid, start_line + rel_idx, line.strip(), m.group(1)))

if violations:
    print(f"Error: [{profile}] 暗号照合ブロック '{target_sym}' (call chain: {' -> '.join(ct_chain)}) 内部に条件分岐命令が検出されました！", file=sys.stderr)
    for fid, line_no, code, inst in violations:
        print(f"  Func {fid} Line {line_no}: [{inst}] -> {code}", file=sys.stderr)
    print("サイドチャネル攻撃(タイミング攻撃)への脆弱性リスクがあるため、ビルドを拒否します。", file=sys.stderr)
    sys.exit(1)

print(f"==> [{profile}] [SUCCESS] Verified {target_sym} call chain ({' -> '.join(ct_chain)}) is completely branch-free (0 conditional branches).")

# subtle の最適化バリア関数(i32.store8 + i32.load8_u の葉関数)を特定.
barrier_funcs = set()
for fid in ct_chain:
    if fid not in funcs:
        continue
    _, f_lines = funcs[fid]
    body_text = "\n".join(f_lines)
    if not call_pattern.search(body_text) and "i32.store8" in body_text and "i32.load8_u" in body_text:
        barrier_funcs.add(fid)

ct_callees = set(ct_chain) - {ct_func_id}

# 4. 本番 X25519 DH (fidelogic_wasm_x25519_dh) における定数時間全ゼロ比較の到達確認.
dh_chain = set(collect_reachable(dh_func_id))
if not (dh_chain & (ct_callees | barrier_funcs)):
    print(f"Error: [{profile}] 'fidelogic_wasm_x25519_dh' (func {dh_func_id}) が定数時間比較/バリア関数へ到達していません。", file=sys.stderr)
    sys.exit(1)
print(f"==> [{profile}] [SUCCESS] Verified fidelogic_wasm_x25519_dh reaches verified branch-free comparator/barrier ({sorted(dh_chain & (ct_callees | barrier_funcs))}).")

# 5. 本番 Vault 復号 (fidelogic_wasm_vault_decrypt) におけるタグ定数時間検証の確認.
if dec_func_id is not None:
    dec_chain = collect_reachable(dec_func_id)
    dec_set = set(dec_chain)
    if not (dec_set & barrier_funcs):
        print(f"Error: [{profile}] 'fidelogic_wasm_vault_decrypt' (func {dec_func_id}) が subtle 定数時間バリアへ到達していません。", file=sys.stderr)
        sys.exit(1)

    # バリアを呼び出すタグ照合関数のループ内部に秘密依存の早期脱出分岐がないことを検証.
    checked_tag_funcs = []
    for fid in dec_chain:
        if fid not in funcs or fid in barrier_funcs:
            continue
        start_line, f_lines = funcs[fid]
        direct_calls = {m.group(1) for line in f_lines for m in call_pattern.finditer(line)}
        if not (direct_calls & barrier_funcs):
            continue
        checked_tag_funcs.append(fid)

        # loop ブロックごとに内部の分岐命令数を検査(先頭の反復継続判定 br_if 1件のみ許容).
        loop_stack = []
        block_depth = 0
        barrier_in_loop = False
        for rel_idx, line in enumerate(f_lines):
            stripped = line.strip()
            if re.match(r'^loop\b', stripped):
                block_depth += 1
                loop_stack.append((block_depth, start_line + rel_idx, [], False))
            elif re.match(r'^(block|if)\b', stripped):
                block_depth += 1
                if re.match(r'^if\b', stripped) and loop_stack:
                    loop_stack[-1][2].append((start_line + rel_idx, stripped, "if"))
            elif stripped == "end":
                if loop_stack and loop_stack[-1][0] == block_depth:
                    _, l_start, l_branches, has_barrier_call = loop_stack.pop()
                    if has_barrier_call:
                        barrier_in_loop = True
                        # ループ内では終端条件用の br_if 1件のみ許容し、if / br_table や複数 br_if を禁止.
                        non_br_if = [b for b in l_branches if b[2] != "br_if"]
                        if non_br_if or len(l_branches) > 1:
                            print(f"Error: [{profile}] fidelogic_wasm_vault_decrypt 配下のタグ照合関数 func {fid} (loop L{l_start}) に不正な分岐が検出されました: {l_branches}", file=sys.stderr)
                            sys.exit(1)
                block_depth -= 1
            else:
                if loop_stack:
                    for m_call in call_pattern.finditer(line):
                        if m_call.group(1) in barrier_funcs:
                            loop_stack[-1] = (loop_stack[-1][0], loop_stack[-1][1], loop_stack[-1][2], True)
                    m_br = branch_pattern.search(line)
                    if m_br:
                        loop_stack[-1][2].append((start_line + rel_idx, stripped, m_br.group(1)))

        # 完全アンロール展開等によりループ内にバリア呼び出しが存在しない場合の非ループ展開検証.
        if not barrier_in_loop:
            func_branches = []
            for rel_idx, line in enumerate(f_lines):
                m_br = branch_pattern.search(line)
                if m_br:
                    func_branches.append((start_line + rel_idx, line.strip(), m_br.group(1)))
            non_br_if = [b for b in func_branches if b[2] != "br_if"]
            if non_br_if or len(func_branches) > 1:
                print(f"Error: [{profile}] fidelogic_wasm_vault_decrypt 配下の非ループ展開タグ照合関数 func {fid} に秘密依存の分岐が検出されました: {func_branches}", file=sys.stderr)
                sys.exit(1)

    if not checked_tag_funcs:
        print(f"Error: [{profile}] 'fidelogic_wasm_vault_decrypt' 配下に subtle バリアを直接呼び出すタグ照合関数が検出されませんでした (checked_tag_funcs is empty)。", file=sys.stderr)
        sys.exit(1)

    print(f"==> [{profile}] [SUCCESS] Verified fidelogic_wasm_vault_decrypt tag comparison (funcs {checked_tag_funcs}) preserves subtle barrier without early-exit branches.")
EOF
}

LITE_WAT="${TARGET_DIR}/fidelogic_lite.wat"
VAULT_WAT="${TARGET_DIR}/fidelogic_vault.wat"

inspect_wat "${LITE_WASM}" "${LITE_WAT}" "profile-lite"
inspect_wat "${VAULT_WASM}" "${VAULT_WAT}" "profile-vault"

# GitHub Actions Step Summary の出力
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then
  {
    echo "### Constant-Time Crypto Verification Summary"
    echo ""
    echo "| Profile | Checked Targets | Result |"
    echo "| :--- | :--- | :--- |"
    echo "| \`profile-lite\` | \`${TARGET_SYMBOL}\` (transitive 0-branch), \`fidelogic_wasm_x25519_dh\` | **PASS** |"
    echo "| \`profile-vault\` | \`${TARGET_SYMBOL}\` (transitive 0-branch), \`fidelogic_wasm_x25519_dh\`, \`fidelogic_wasm_vault_decrypt\` (tag ct_eq) | **PASS** |"
    echo ""
    echo "WebAssembly逆アセンブル解析により、暗号照合ブロックの呼び出しチェーン全体の無分岐性および本番復号・鍵共有での定数時間比較保持を確認しました。"
  } >> "${GITHUB_STEP_SUMMARY}"
fi

echo ""
echo "==> [SUCCESS] All target Wasm binaries verified branch-free for constant-time operations."
