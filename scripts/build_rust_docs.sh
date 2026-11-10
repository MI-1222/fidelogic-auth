#!/usr/bin/env bash
# Fidelogic Rust API ドキュメント生成スクリプト。
# cargo doc を実行し、全クレートの HTML リファレンスを public/rustdoc/ に配置する。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

RUSTDOC_OUT="${REPO_ROOT}/public/rustdoc"
mkdir -p "${RUSTDOC_OUT}"

if ! command -v cargo >/dev/null 2>&1; then
  echo "Error: 'cargo' が見つかりません。Rust ツールチェーンを導入してください。" >&2
  exit 1
fi

echo "==> Building Rust workspace API documentation via cargo doc..."
# サンドボックス環境下での git 設定読み込み制限を回避。
GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null \
  cargo doc --workspace --no-deps --all-features

echo "==> Deploying API documentation to ${RUSTDOC_OUT}..."
cp -R "${REPO_ROOT}/target/doc/"* "${RUSTDOC_OUT}/"

# rustdoc ルートへのリダイレクト HTML を作成。
cat << 'EOF' > "${RUSTDOC_OUT}/index.html"
<!DOCTYPE html>
<html lang="ja">
<head>
  <meta charset="utf-8">
  <meta http-equiv="refresh" content="0; url=fidelogic_core/index.html">
  <title>Fidelogic Rust API Documentation</title>
  <script>window.location.replace("fidelogic_core/index.html");</script>
</head>
<body>
  <p>リダイレクトしています... <a href="fidelogic_core/index.html">fidelogic_core ドキュメントはこちら</a></p>
</body>
</html>
EOF

echo "==> [SUCCESS] Rust API ドキュメントの生成が完了しました: ${RUSTDOC_OUT}"
