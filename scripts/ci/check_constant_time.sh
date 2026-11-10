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

  echo "==> [${profile_name}] Inspecting WAT for branch instructions in ${TARGET_SYMBOL}..."

  python3 - <<EOF
import re
import sys

wat_path = "${wat_file}"
target_sym = "${TARGET_SYMBOL}"
profile = "${profile_name}"

with open(wat_path, "r", encoding="utf-8") as f:
    content = f.read()

# 1. エクスポートシンボルから関数ID(数値または識別子)を探索
export_pattern = r'\(export\s+"' + re.escape(target_sym) + r'"\s+\(func\s+(?:\$)?([0-9a-zA-Z_.]+)\)\)'
export_match = re.search(export_pattern, content)

func_id = None
if export_match:
    func_id = export_match.group(1)
else:
    # 直接関数名がアタッチされているケースを探索
    named_func_pattern = r'\(func\s+\$' + re.escape(target_sym) + r'\b'
    if re.search(named_func_pattern, content):
        func_id = target_sym

if not func_id:
    print(f"Error: [{profile}] WAT内にエクスポートシンボル '{target_sym}' が見つかりません。", file=sys.stderr)
    sys.exit(1)

# 2. 関数本体の行ブロックを抽出
lines = content.splitlines()
in_target_func = False
func_lines = []
paren_depth = 0

# 関数開始パターンの決定
if func_id.isdigit():
    func_start_pattern = re.compile(r'^\s*\(func\s+\(;' + func_id + r';\)')
else:
    func_start_pattern = re.compile(r'^\s*\(func\s+\$' + re.escape(func_id) + r'\b')

for line in lines:
    if not in_target_func:
        if func_start_pattern.search(line):
            in_target_func = True
            func_lines.append(line)
            paren_depth += line.count('(') - line.count(')')
    else:
        func_lines.append(line)
        paren_depth += line.count('(') - line.count(')')
        if paren_depth <= 0:
            break

if not func_lines:
    print(f"Error: [{profile}] 関数 '{target_sym}' (id: {func_id}) の定義ブロックを抽出できませんでした。", file=sys.stderr)
    sys.exit(1)

func_body = "\n".join(func_lines)

# 3. 条件分岐命令(br_if, if, br_table)の静的検出
branch_pattern = re.compile(r'\b(br_if|if|br_table)\b')
violations = []
for idx, line in enumerate(func_lines, start=1):
    m = branch_pattern.search(line)
    if m:
        violations.append((idx, line.strip(), m.group(1)))

if violations:
    print(f"Error: [{profile}] 暗号照合ブロック '{target_sym}' 内部に条件分岐命令が検出されました！", file=sys.stderr)
    for line_no, code, inst in violations:
        print(f"  Line {line_no}: [{inst}] -> {code}", file=sys.stderr)
    print("サイドチャネル攻撃(タイミング攻撃)への脆弱性リスクがあるため、ビルドを拒否します。", file=sys.stderr)
    sys.exit(1)

print(f"==> [{profile}] [SUCCESS] Verified {target_sym} is completely branch-free (0 conditional branches).")
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
    echo "| Profile | Target Function | Forbidden Branches (\`br_if\`, \`if\`, \`br_table\`) | Result |"
    echo "| :--- | :--- | :--- | :--- |"
    echo "| \`profile-lite\` | \`${TARGET_SYMBOL}\` | 0 detected | **PASS** |"
    echo "| \`profile-vault\` | \`${TARGET_SYMBOL}\` | 0 detected | **PASS** |"
    echo ""
    echo "WebAssembly逆アセンブル解析により、暗号照合ブロック内部の完全な分岐命令不在(定数時間性)を確認しました。"
  } >> "${GITHUB_STEP_SUMMARY}"
fi

echo ""
echo "==> [SUCCESS] All target Wasm binaries verified branch-free for constant-time operations."
