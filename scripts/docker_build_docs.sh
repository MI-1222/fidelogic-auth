#!/usr/bin/env bash
# Docker コンテナ内で Rocq 証明の Alectryon HTML 生成を実行するローカル支援スクリプト。
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

IMAGE_NAME="fidelogic-docs-builder"
CONTAINER_NAME="fidelogic-docs-runner-$$"

mkdir -p "${REPO_ROOT}/public"

echo "==> Building Docker image for Alectryon docs..."
docker build --platform linux/amd64 -f Dockerfile.docs -t "${IMAGE_NAME}" .

echo "==> Running Alectryon docs generation in isolated container..."
docker run --name "${CONTAINER_NAME}" --platform linux/amd64 "${IMAGE_NAME}"

echo "==> Extracting generated proofs to host via docker cp..."
rm -rf "${REPO_ROOT}/public/proofs"
docker cp "${CONTAINER_NAME}:/workspace/public/proofs" "${REPO_ROOT}/public/proofs"
docker rm "${CONTAINER_NAME}"

# 統合トップポータルの再配置。
"${REPO_ROOT}/scripts/build_portal.sh"

echo "==> [SUCCESS] Proofs generated and portal updated: ${REPO_ROOT}/public"
