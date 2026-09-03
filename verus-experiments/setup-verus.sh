#!/usr/bin/env bash
set -euo pipefail

RELEASE="0.2026.08.30.b432e82"
ARCHIVE="verus-${RELEASE}-arm64-macos.zip"
SHA256="4eacbfeee673356136b56ad94b4c132e7bbadeb7fcbbcee3231b0a1c1327861d"
RUST_TOOLCHAIN="1.97.1-aarch64-apple-darwin"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS_DIR="${ROOT}/.tools/verus"
INSTALL_DIR="${TOOLS_DIR}/verus-arm64-macos"
ARCHIVE_PATH="${TMPDIR:-/tmp}/${ARCHIVE}"

if [[ "$(uname -s)" != "Darwin" || "$(uname -m)" != "arm64" ]]; then
  echo "This experiment currently pins the macOS ARM64 Verus release." >&2
  exit 1
fi

if [[ ! -x "${HOME}/.cargo/bin/rustup" ]]; then
  echo "Install rustup before running this script: https://rustup.rs" >&2
  exit 1
fi

PATH="${HOME}/.cargo/bin:${PATH}" rustup toolchain install "${RUST_TOOLCHAIN}" --profile minimal
PATH="${HOME}/.cargo/bin:${PATH}" rustup component add rustfmt --toolchain "${RUST_TOOLCHAIN}"

if [[ ! -x "${INSTALL_DIR}/verus" ]]; then
  mkdir -p "${TOOLS_DIR}"
  curl --fail --location \
    "https://github.com/verus-lang/verus/releases/download/release%2F${RELEASE}/${ARCHIVE}" \
    --output "${ARCHIVE_PATH}"
  echo "${SHA256}  ${ARCHIVE_PATH}" | shasum -a 256 --check
  unzip -q "${ARCHIVE_PATH}" -d "${TOOLS_DIR}"
fi

PATH="${HOME}/.cargo/bin:${PATH}" "${INSTALL_DIR}/verus" --version
