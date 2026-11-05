#!/usr/bin/env bash
set -euo pipefail

IMAGE_NAME="fidelogic-proof-checker"

echo "==> Building Docker image..."
docker build --platform linux/amd64 -f Dockerfile.proofs -t "${IMAGE_NAME}" .

echo "==> Running proofs and audit in isolated container..."
docker run --rm --platform linux/amd64 "${IMAGE_NAME}"
