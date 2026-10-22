#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_DIR="${ROOT}/.tools/verus/verus-arm64-macos"

if [[ ! -x "${VERUS_DIR}/cargo-verus" ]]; then
  echo "Run verus-experiments/setup-verus.sh first." >&2
  exit 1
fi

export PATH="${VERUS_DIR}:${HOME}/.cargo/bin:${PATH}"

cd "${ROOT}"

lake build Triptych.Backend.Verus Triptych.Backend.VerusTests

(
  cd "${ROOT}/cedar-examples"
  lake build Inputs.Decimal Inputs.Duration Inputs.Datetime Inputs.IPv4 Inputs.IPv6
)

(
  cd "${ROOT}/verus-experiments/runtime"
  cargo verus verify --offline --locked --fwd-verus-args-to roots -- \
    --no-cheating --multiple-errors 20
)

(
  cd "${ROOT}/verus-experiments/grammar-coverage"
  cargo verus verify --offline --locked --fwd-verus-args-to roots -- \
    --no-cheating --multiple-errors 20
)

extension_status=0
for extension in decimal duration datetime ipaddr; do
  if ! (
    cd "${ROOT}/verus-experiments/cedar-ext/${extension}"
    cargo verus verify --offline --locked --fwd-verus-args-to roots -- \
      --no-cheating --multiple-errors 20
    cargo test --offline --locked
  ); then
    extension_status=1
    echo "FAILED: cedar-ext/${extension}" >&2
  fi
done

exit "${extension_status}"
