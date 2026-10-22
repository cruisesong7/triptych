#!/usr/bin/env bash
set -euo pipefail

RELEASE="0.2026.08.30.b432e82"
RUST_VERSION="1.97.1"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)
    PLATFORM="arm64-macos"
    SHA256="4eacbfeee673356136b56ad94b4c132e7bbadeb7fcbbcee3231b0a1c1327861d"
    RUST_TOOLCHAIN="${RUST_VERSION}-aarch64-apple-darwin"
    ;;
  Linux-x86_64)
    PLATFORM="x86-linux"
    SHA256="067f5f72a457fe66b77c0c10b180f2a919a9c7481a8baa024ffc716aa931a41b"
    RUST_TOOLCHAIN="${RUST_VERSION}-x86_64-unknown-linux-gnu"
    ;;
  *)
    echo "No pinned Verus release for $(uname -s)-$(uname -m)." >&2
    exit 1
    ;;
esac

ARCHIVE="verus-${RELEASE}-${PLATFORM}.zip"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS_DIR="${ROOT}/.tools/verus"
INSTALL_DIR="${TOOLS_DIR}/verus-${PLATFORM}"
ARCHIVE_PATH="${TMPDIR:-/tmp}/${ARCHIVE}"

if ! command -v rustup >/dev/null 2>&1 && [[ ! -x "${HOME}/.cargo/bin/rustup" ]]; then
  echo "Install rustup before running this script: https://rustup.rs" >&2
  exit 1
fi
export PATH="${HOME}/.cargo/bin:${PATH}"

rustup toolchain install "${RUST_TOOLCHAIN}" --profile minimal
rustup component add rustfmt --toolchain "${RUST_TOOLCHAIN}"

if [[ ! -x "${INSTALL_DIR}/verus" ]]; then
  mkdir -p "${TOOLS_DIR}"
  curl --fail --location \
    "https://github.com/verus-lang/verus/releases/download/release%2F${RELEASE}/${ARCHIVE}" \
    --output "${ARCHIVE_PATH}"
  if command -v sha256sum >/dev/null 2>&1; then
    echo "${SHA256}  ${ARCHIVE_PATH}" | sha256sum --check
  else
    echo "${SHA256}  ${ARCHIVE_PATH}" | shasum -a 256 --check
  fi
  unzip -q "${ARCHIVE_PATH}" -d "${TOOLS_DIR}"
fi

"${INSTALL_DIR}/verus" --version
