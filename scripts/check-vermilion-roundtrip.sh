#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: $0 --vermilion-root DIR --artifact-dir DIR --proof-file FILE --source-project DIR" >&2
}

vermilion_root=""
artifact_dir=""
proof_file=""
source_project=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --vermilion-root)
      vermilion_root="$2"
      shift 2
      ;;
    --artifact-dir)
      artifact_dir="$2"
      shift 2
      ;;
    --proof-file)
      proof_file="$2"
      shift 2
      ;;
    --source-project)
      source_project="$2"
      shift 2
      ;;
    *)
      usage
      exit 2
      ;;
  esac
done

if [[ -z "$vermilion_root" || -z "$artifact_dir" || -z "$proof_file" \
  || -z "$source_project" ]]; then
  usage
  exit 2
fi

vermilion_root="$(cd "$vermilion_root" && pwd -P)"
artifact_dir="$(cd "$artifact_dir" && pwd -P)"
proof_file="$(cd "$(dirname "$proof_file")" && pwd -P)/$(basename "$proof_file")"
source_project="$(cd "$source_project" && pwd -P)"

manifest="$artifact_dir/manifest.txt"
for required in "$manifest" "$artifact_dir/spec.rs" "$proof_file" \
  "$vermilion_root/scripts/run_example.sh" "$vermilion_root/lean-toolchain" \
  "$source_project/lean-toolchain"; do
  if [[ ! -e "$required" ]]; then
    echo "Triptych: missing Vermilion roundtrip input: $required" >&2
    exit 2
  fi
done

manifest_value() {
  local key="$1"
  sed -n "s/^${key}=//p" "$manifest"
}

format_name="$(manifest_value format)"
crate_stem="$(manifest_value crate_stem)"
source_module="$(manifest_value source_module)"
contract_module="$(manifest_value contract_module)"
recovered_module="$(manifest_value recovered_module)"
proof_module="$(manifest_value proof_module)"
check_module="$(manifest_value check_module)"
obligations="$(manifest_value obligation)"

if [[ -z "$format_name" || -z "$crate_stem" || -z "$source_module" \
  || -z "$contract_module" || -z "$recovered_module" || -z "$proof_module" \
  || -z "$check_module" \
  || -z "$obligations" ]]; then
  echo "Triptych: incomplete Vermilion roundtrip manifest: $manifest" >&2
  exit 2
fi

source_toolchain="$(tr -d '[:space:]' < "$source_project/lean-toolchain")"
vermilion_toolchain="$(tr -d '[:space:]' < "$vermilion_root/lean-toolchain")"
if [[ "$source_toolchain" != "$vermilion_toolchain" ]]; then
  echo "Triptych: Vermilion Lean toolchain mismatch" >&2
  echo "  source project: $source_toolchain" >&2
  echo "  Vermilion:      $vermilion_toolchain" >&2
  echo "Use a pinned Vermilion compatibility revision before checking the roundtrip." >&2
  exit 2
fi

# Record which Vermilion produced the recovered definitions. Known-good builds are not always git
# checkouts, so fall back to a fingerprint of the toolchain and dependency pins.
if vermilion_revision="$(git -C "$vermilion_root" rev-parse HEAD 2>/dev/null)"; then
  if [[ -n "$(git -C "$vermilion_root" status --porcelain 2>/dev/null)" ]]; then
    vermilion_revision="$vermilion_revision (dirty)"
  fi
else
  vermilion_revision="no git metadata; lake-manifest sha256 $(
    shasum -a 256 "$vermilion_root/lake-manifest.json" | cut -d' ' -f1)"
fi
echo "Triptych: Vermilion $vermilion_root"
echo "  toolchain: $vermilion_toolchain"
echo "  revision:  $vermilion_revision"
printf 'vermilion_root=%s\nvermilion_toolchain=%s\nvermilion_revision=%s\n' \
  "$vermilion_root" "$vermilion_toolchain" "$vermilion_revision" \
  > "$artifact_dir/vermilion.txt"

echo "Triptych: running generated $format_name specification through Vermilion"
"$vermilion_root/scripts/run_example.sh" \
  "$artifact_dir" "$crate_stem.rs" --per-function

vermilion_specs="$artifact_dir/generated/$crate_stem/Specs.lean"
recovered_specs="$artifact_dir/${recovered_module//.//}.lean"
contract_source="$artifact_dir/${contract_module//.//}.lean"
if [[ ! -f "$vermilion_specs" ]]; then
  echo "Triptych: Vermilion did not emit recovered specifications: $vermilion_specs" >&2
  exit 1
fi
# Vermilion names its output `generated.<crate>.Specs`; Triptych compiles it under its own module
# name so it never collides with Vermilion's `generated.*` library in a shared Lake workspace.
mkdir -p "$(dirname "$recovered_specs")"
cp "$vermilion_specs" "$recovered_specs"
if [[ ! -f "$contract_source" ]]; then
  echo "Triptych: generated roundtrip contract is missing: $contract_source" >&2
  exit 1
fi

# Publish this run's generated modules to the roundtrip Lake package beside the proofs, so the
# editor and `lake build` there elaborate the proofs against the latest translation.
package_root="$(cd "$(dirname "$proof_file")/../.." && pwd -P)"
if [[ -f "$package_root/lakefile.lean" && -f "$package_root/lake-manifest.json" ]]; then
  # Its manifest pins every git dependency to the revisions Vermilion and cedar-examples already
  # build. Link those checkouts instead of letting Lake clone and rebuild Mathlib a second time.
  mkdir -p "$package_root/.lake/packages"
  while IFS= read -r dependency; do
    link="$package_root/.lake/packages/$dependency"
    [[ -e "$link" ]] && continue
    for candidate in "$vermilion_root/.lake/packages/$dependency" \
      "$source_project/.lake/packages/$dependency"; do
      if [[ -d "$candidate" ]]; then
        ln -s "$candidate" "$link"
        break
      fi
    done
  done < <(sed -n 's/^ *"name": "\([^"]*\)",$/\1/p' "$package_root/lake-manifest.json")

  for published in "$recovered_module" "$contract_module"; do
    published_target="$package_root/generated-src/${published//.//}.lean"
    mkdir -p "$(dirname "$published_target")"
    cp "$artifact_dir/${published//.//}.lean" "$published_target"
  done
fi

echo "Triptych: building original Lean specification module $source_module"
(
  cd "$source_project"
  lake build "$source_module"
)

proof_target="$artifact_dir/${proof_module//.//}.lean"
mkdir -p "$(dirname "$proof_target")"
cp "$proof_file" "$proof_target"
utils_source="$(dirname "$proof_file")/Utils.lean"
utils_target="$artifact_dir/TriptychVermilionProofs/Utils.lean"
if [[ ! -f "$utils_source" ]]; then
  echo "Triptych: missing shared Vermilion proof support: $utils_source" >&2
  exit 2
fi
mkdir -p "$(dirname "$utils_target")"
cp "$utils_source" "$utils_target"

# `<Format>.lean` states the public theorems; its helper modules live in `<Format>/`, as in
# Cedar's `Thm/Ext/<Format>/Lemmas.lean` layout.
lemma_source_dir="${proof_file%.lean}"
lemma_target_dir="${proof_target%.lean}"
lemma_targets=()
if [[ -d "$lemma_source_dir" ]]; then
  rm -rf "$lemma_target_dir"
  mkdir -p "$lemma_target_dir"
  cp -R "$lemma_source_dir"/. "$lemma_target_dir"/
  while IFS= read -r lemma_file; do
    lemma_targets+=("$lemma_file")
  done < <(find "$lemma_target_dir" -name '*.lean' | sort)
fi

check_source="$artifact_dir/${check_module//.//}.lean"
if [[ ! -f "$check_source" ]]; then
  echo "Triptych: generated roundtrip check module is missing: $check_source" >&2
  exit 1
fi

source_lean_path="$(
  cd "$source_project"
  lake env printenv LEAN_PATH
)"
vermilion_lean_path="$(
  cd "$vermilion_root"
  source scripts/lean_env.sh
  printf '%s' "$LEAN_PATH"
)"
combined_lean_path="$source_lean_path:$artifact_dir:$vermilion_lean_path"

lean_binary="$(
  cd "$source_project"
  lake env which lean
)"
lean_command=("$lean_binary")
for plugin in \
  "$vermilion_root/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.dylib" \
  "$vermilion_root/.lake/packages/cvc5/.lake/build/lib/libcvc5_cvc5.so"; do
  if [[ -f "$plugin" ]]; then
    lean_command+=("--plugin=$plugin")
    break
  fi
done

compile_module() {
  local source="$1"
  local output="${source%.lean}.olean"
  local relative_source="${source#"$artifact_dir"/}"
  local relative_output="${output#"$artifact_dir"/}"
  (
    cd "$artifact_dir"
    LEAN_PATH="$combined_lean_path" "${lean_command[@]}" \
      -o "$relative_output" "$relative_source"
  )
}

module_of() {
  local relative="${1#"$artifact_dir"/}"
  relative="${relative%.lean}"
  printf '%s' "${relative//\//.}"
}

# Compile helper modules in import order: each pass compiles every module whose
# `TriptychVermilionProofs.<Format>.*` imports are already built.
compile_lemma_modules() {
  local pending=("${lemma_targets[@]}")
  local built=" "
  while [[ ${#pending[@]} -gt 0 ]]; do
    local remaining=()
    local progressed=false
    local lemma_file
    for lemma_file in "${pending[@]}"; do
      local ready=true
      local dependency
      for dependency in $(sed -n "s/^import \(${proof_module//./\\.}\.[A-Za-z0-9_.]*\).*/\1/p" "$lemma_file"); do
        if [[ "$built" != *" $dependency "* ]]; then
          ready=false
        fi
      done
      if $ready; then
        compile_module "$lemma_file"
        built="$built$(module_of "$lemma_file") "
        progressed=true
      else
        remaining+=("$lemma_file")
      fi
    done
    if ! $progressed; then
      echo "Triptych: unresolvable imports among proof modules in $lemma_target_dir" >&2
      exit 1
    fi
    pending=("${remaining[@]+"${remaining[@]}"}")
  done
}

compile_module "$recovered_specs"
compile_module "$utils_target"
compile_module "$contract_source"
if [[ ${#lemma_targets[@]} -gt 0 ]]; then
  compile_lemma_modules
fi
compile_module "$proof_target"

axiom_report="$artifact_dir/axioms.txt"
relative_check_source="${check_source#"$artifact_dir"/}"
(
  cd "$artifact_dir"
  LEAN_PATH="$combined_lean_path" "${lean_command[@]}" \
    "$relative_check_source"
) | tee "$axiom_report"

if grep -q 'sorryAx' "$axiom_report"; then
  echo "Triptych: a Vermilion roundtrip theorem still depends on sorryAx" >&2
  exit 1
fi

# Every theorem may depend only on Lean's standard axioms. This rejects leftover debugging
# axioms and `native_decide` (`Lean.ofReduceBool`) as well as `sorry`.
allowed_axioms="propext Classical.choice Quot.sound"
unexpected_axioms="$(
  tr '\n' ' ' < "$axiom_report" \
    | grep -o 'depends on axioms: \[[^]]*\]' \
    | sed -e 's/^depends on axioms: \[//' -e 's/\]$//' \
    | tr ',' '\n' | tr -d ' ' | sort -u \
    | grep -vxF -e propext -e Classical.choice -e Quot.sound || true
)"
if [[ -n "$unexpected_axioms" ]]; then
  echo "Triptych: Vermilion roundtrip theorems depend on axioms outside {$allowed_axioms}:" >&2
  echo "$unexpected_axioms" | sed 's/^/  /' >&2
  exit 1
fi
expected_theorems="$(manifest_value obligation | wc -l | tr -d ' ')"
reported_theorems="$(tr '\n' ' ' < "$axiom_report" | grep -o "' \(depends on axioms\|does not depend on any axioms\)" | wc -l | tr -d ' ')"
if [[ "$reported_theorems" != "$expected_theorems" ]]; then
  echo "Triptych: axiom report covers $reported_theorems theorems; manifest lists $expected_theorems" >&2
  exit 1
fi

echo "Triptych: every Vermilion semantic roundtrip theorem verified for $format_name"
