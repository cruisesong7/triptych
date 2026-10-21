#!/usr/bin/env bash
# Verify every generated Verus crate with `--no-cheating`.
#
# Usage: verify.sh [--without-dev-deps]
#
# `--without-dev-deps` verifies a temporary copy of the crates whose manifests omit
# `[dev-dependencies]` and `[[bench]]` targets, resolving against the committed lockfiles. Those sections only serve the Cedar conformance
# tests and benchmarks, which need a sibling Cedar Rust checkout; verification does not use them.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_DIR="$(ls -d "${ROOT}"/.tools/verus/verus-*/ 2>/dev/null | head -n 1)"
VERUS_DIR="${VERUS_DIR%/}"

if [[ -z "${VERUS_DIR}" || ! -x "${VERUS_DIR}/cargo-verus" ]]; then
  echo "Run verus-experiments/setup-verus.sh first." >&2
  exit 1
fi

export PATH="${VERUS_DIR}:${HOME}/.cargo/bin:${PATH}"

CRATES=(
  grammar-coverage
  direct-coverage
  search-order
  cedar-ext/decimal
  cedar-ext/suite
)

EXPERIMENTS="${ROOT}/verus-experiments"
CARGO_FLAGS=(--offline --locked)

if [[ "${1:-}" == "--without-dev-deps" ]]; then
  WORK="$(mktemp -d)"
  trap 'rm -rf "${WORK}"' EXIT
  # Copy the whole tree: crates include sibling generated sources by relative path.
  (cd "${EXPERIMENTS}" && tar --exclude=target -cf - .) | (cd "${WORK}" && tar -xf -)
  for crate in "${CRATES[@]}"; do
    rm -rf "${WORK}/${crate}/benches" "${WORK}/${crate}/tests"
    # Drop whole `[dev-dependencies]` and `[[bench]]` tables, keeping every other table.
    awk '
      /^\[/ { skip = ($0 == "[dev-dependencies]" || $0 == "[[bench]]") }
      !skip { print }
    ' "${EXPERIMENTS}/${crate}/Cargo.toml" > "${WORK}/${crate}/Cargo.toml"
  done
  EXPERIMENTS="${WORK}"
  # The committed lockfiles stay in place: without `--locked`, Cargo only prunes the removed
  # dev-dependencies and keeps every other resolved version pinned.
  CARGO_FLAGS=()
fi

for crate in "${CRATES[@]}"; do
  echo "== verifying ${crate}"
  (
    cd "${EXPERIMENTS}/${crate}"
    cargo verus verify ${CARGO_FLAGS[@]+"${CARGO_FLAGS[@]}"} --fwd-verus-args-to roots -- \
      --no-cheating --multiple-errors 20
  )
done
