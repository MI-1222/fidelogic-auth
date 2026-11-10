#!/usr/bin/env bash
# Fidelogic Rocq 形式検証証明 (Alectryon) ドキュメント生成スクリプト。
# Rocq 理論を Dune でビルド後、Alectryon を用いて対話的証明 HTML を public/proofs/ に生成する。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

PROOFS_OUT="${REPO_ROOT}/public/proofs"
mkdir -p "${PROOFS_OUT}"

# 1. opam 環境の読み込み。
if [ -z "${OPAM_SWITCH_PREFIX:-}" ] && command -v opam >/dev/null 2>&1; then
  eval "$(opam env)" || true
fi

# 2. Rocq 理論のビルド (依存 .vo ファイル群の事前生成)。
echo "==> Compiling Rocq proof theories via Dune..."
if [ -f "${REPO_ROOT}/scripts/build_proofs.sh" ]; then
  "${REPO_ROOT}/scripts/build_proofs.sh" || {
    echo "Warning: Dune ビルドに失敗または警告が発生しました。処理を継続します。"
  }
fi

# 3. Alectryon 実行コマンドの検出。
export PATH="${HOME}/.local/bin:${PATH}"
ALECTRYON_CMD=""
if command -v alectryon >/dev/null 2>&1; then
  ALECTRYON_CMD="alectryon"
elif python3 -m alectryon --version >/dev/null 2>&1; then
  ALECTRYON_CMD="python3 -m alectryon"
elif [ -f "${REPO_ROOT}/.local/alectryon/alectryon.py" ]; then
  ALECTRYON_CMD="python3 ${REPO_ROOT}/.local/alectryon/alectryon.py"
fi

if [ -z "${ALECTRYON_CMD}" ]; then
  echo "Error: Alectryon が見つかりません。pip install alectryon を実行してください。" >&2
  exit 1
fi

echo "==> Alectryon コマンド: ${ALECTRYON_CMD}"

# 4. 対象ファイルリスト。
THEORY_FILES=(
  "proofs/Tactics.v"
  "proofs/Theories/EnvelopeFsm.v"
  "proofs/Theories/FidelogicCore.v"
  "proofs/Theories/NonInterference.v"
  "proofs/Theories/PrecisProfile.v"
  "proofs/Theories/TlvRoundtrip.v"
  "proofs/Theories/TlvSoundness.v"
  "proofs/Theories/TlvTotality.v"
)

# ドライバー引数の決定 (環境変数 ALECTRYON_DRIVER で上書き可能。指定がない場合は自動検出に委ねる)。
DRIVER_OPT=()
if [ -n "${ALECTRYON_DRIVER:-}" ]; then
  DRIVER_OPT=(--coq-driver "${ALECTRYON_DRIVER}")
elif command -v vsrocqtop >/dev/null 2>&1; then
  DRIVER_OPT=(--coq-driver vsrocq)
fi

echo "==> Translating Rocq source files to interactive Alectryon HTML..."
for vfile in "${THEORY_FILES[@]}"; do
  if [ -f "${REPO_ROOT}/${vfile}" ]; then
    base_name="$(basename "${vfile}" .v)"
    out_html="${PROOFS_OUT}/${base_name}.html"
    echo "    Processing: ${vfile} -> ${out_html}"

    ${ALECTRYON_CMD} \
      --frontend coq \
      --backend webpage \
      --copy-assets copy \
      --webpage-style windowed \
      ${DRIVER_OPT[@]+"${DRIVER_OPT[@]}"} \
      -Q "${REPO_ROOT}/_build/default/proofs" Fidelogic \
      -Q "${REPO_ROOT}/proofs" Fidelogic \
      -o "${out_html}" \
      "${REPO_ROOT}/${vfile}" || {
        echo "    [Warning] 対話モード生成に失敗したため、静的ハイライト (--coq-driver noop) で再試行します。"
        ${ALECTRYON_CMD} \
          --frontend coq \
          --backend webpage \
          --coq-driver noop \
          --copy-assets copy \
          --webpage-style windowed \
          -o "${out_html}" \
          "${REPO_ROOT}/${vfile}"
      }
  fi
done

# 5. 証明一覧ページ (public/proofs/index.html) の配置。
echo "==> Deploying proofs index page from .github/pages/proofs.html..."
PROOFS_TEMPLATE="${REPO_ROOT}/.github/pages/proofs.html"
if [ ! -f "${PROOFS_TEMPLATE}" ]; then
  echo "Error: ${PROOFS_TEMPLATE} が見つかりません。" >&2
  exit 1
fi
cp "${PROOFS_TEMPLATE}" "${PROOFS_OUT}/index.html"

echo "==> [SUCCESS] Rocq 形式検証証明 (Alectryon) ドキュメントの生成が完了しました: ${PROOFS_OUT}"
