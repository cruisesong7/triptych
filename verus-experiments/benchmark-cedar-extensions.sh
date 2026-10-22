#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RESULT_DIR="${ROOT}/verus-experiments/benchmark-results"
RESULT_FILE="${RESULT_DIR}/latest.txt"

mkdir -p "${RESULT_DIR}"

{
  echo "Cedar extension parser benchmark"
  echo "timestamp_utc: $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo "triptych_commit: $(git -C "${ROOT}" rev-parse HEAD)"
  echo "triptych_worktree_changes: $(git -C "${ROOT}" status --porcelain | wc -l | tr -d ' ')"
  echo "cedar_commit: $(git -C "${ROOT}/../cedar" rev-parse HEAD)"
  echo "cedar_worktree_changes: $(git -C "${ROOT}/../cedar" status --porcelain | wc -l | tr -d ' ')"
  echo "rustc: $(rustc --version)"
  echo "cargo: $(cargo --version)"
  echo "host: $(uname -m) $(uname -s) $(uname -r)"
  echo
  echo "Benchmark harnesses:"
  echo "  decimal: verus-experiments/cedar-ext/decimal/benches/runtime.rs"
  echo "  duration: verus-experiments/cedar-ext/duration/benches/runtime.rs"
  echo "  datetime: verus-experiments/cedar-ext/datetime/benches/runtime.rs"
  echo "  ipaddr: verus-experiments/cedar-ext/ipaddr/benches/runtime.rs"
  echo
  echo "Cedar production parser sources:"
  echo "  decimal: cedar-policy-core/src/extensions/decimal.rs"
  echo "  duration/datetime: cedar-policy-core/src/extensions/datetime.rs"
  echo "  ipaddr: cedar-policy-core/src/extensions/ipaddr.rs"
  echo
  echo "Timed representative inputs:"
  echo "  decimal: -1234567890.1234 (5,000,000 iterations/round)"
  echo "  duration: -12d23h59m59s999ms (2,000,000 iterations/round)"
  echo "  datetime: 2024-01-15T10:30:45.123-0800 (2,000,000 iterations/round)"
  echo "  ipaddr: 2001:db8:85a3::8a2e:370:7334/64 (2,000,000 iterations/round)"
  echo "  rounds: 7, alternating verified/Cedar execution order"
  echo "  timing: std::time::Instant, optimized Cargo bench profile"
  echo "  barriers: input and complete output pass through std::hint::black_box"
  echo
  echo "Differential regression sources:"
  echo "  decimal: verus-experiments/cedar-ext/decimal/tests/"
  echo "  duration: verus-experiments/cedar-ext/duration/tests/regression.rs"
  echo "  datetime: verus-experiments/cedar-ext/datetime/tests/regression.rs"
  echo "  ipaddr: verus-experiments/cedar-ext/ipaddr/tests/regression.rs"
  echo

  for extension in decimal duration datetime ipaddr; do
    echo "== ${extension} =="
    cargo bench \
      --manifest-path "${ROOT}/verus-experiments/cedar-ext/${extension}/Cargo.toml" \
      --bench runtime --offline --locked
    echo
  done
} 2>&1 | tee "${RESULT_FILE}"
