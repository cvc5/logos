#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

readonly forbidden_pattern="(^|[^[:alnum:]_'])(sorry|admit|axiom)([^[:alnum:]_']|$)"
# Tactics and terms that trust compiled code (the axiom `Lean.ofReduceBool`
# or `Lean.ofReduceNat`) rather than the kernel: `native_decide`,
# `decide +native`, `bv_decide`, and the axioms themselves.
readonly native_pattern="(^|[^[:alnum:]_'])(native_decide|bv_decide|ofReduceBool|ofReduceNat|reduceBool|reduceNat)([^[:alnum:]_'?!]|$)|[+]native([^[:alnum:]_']|$)|native[[:space:]]*:=[[:space:]]*true"
readonly source_dirs=(Cpc CpcMini)

for source_dir in "${source_dirs[@]}"; do
  if [ ! -d "${source_dir}" ]; then
    echo "error: source directory not found: ${source_dir}" >&2
    exit 1
  fi
done

source_files=()
while IFS= read -r -d '' source_file; do
  source_files+=("${source_file}")
done < <(find "${source_dirs[@]}" -type f -name '*.lean' -print0)

if [ "${#source_files[@]}" -eq 0 ]; then
  echo "error: no Lean source files found under Cpc or CpcMini" >&2
  exit 1
fi

# Fail with `message` if `pattern` occurs in a source file.
check_absent() {
  local pattern="$1" message="$2" grep_status=0
  LC_ALL=C grep -nHE "${pattern}" "${source_files[@]}" || grep_status=$?
  case "${grep_status}" in
    0)
      echo "error: ${message}" >&2
      exit 1
      ;;
    1)
      ;;
    *)
      echo "error: failed to scan Lean source files" >&2
      exit "${grep_status}"
      ;;
  esac
}

check_absent "${forbidden_pattern}" \
  "forbidden proof escape hatch found in Cpc or CpcMini
Remove every standalone 'sorry', 'admit', and 'axiom' token, including occurrences in comments."

check_absent "${native_pattern}" \
  "proof by native evaluation found in Cpc or CpcMini
'native_decide', 'decide +native' and 'bv_decide' add Lean.ofReduceBool, which trusts the
compiler and every @[extern]/@[implemented_by] implementation. Use 'decide +kernel' (or 'decide',
'rfl', 'simp') so the proof is checked by the kernel alone."

echo "Proof hygiene check passed (${#source_files[@]} Lean source files checked)."
