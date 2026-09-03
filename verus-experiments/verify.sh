#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_DIR="${ROOT}/.tools/verus/verus-arm64-macos"

if [[ ! -x "${VERUS_DIR}/cargo-verus" ]]; then
  echo "Run verus-experiments/setup-verus.sh first." >&2
  exit 1
fi

export PATH="${VERUS_DIR}:${HOME}/.cargo/bin:${PATH}"

(
  cd "${ROOT}/verus-experiments/cedar-ext/decimal"
  cargo verus verify --locked --fwd-verus-args-to roots -- --no-cheating
)
