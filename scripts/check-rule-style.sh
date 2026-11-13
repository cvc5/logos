#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
rules_dir="${repo_root}/Cpc/Proofs/Rules"

if [ ! -d "${rules_dir}" ]; then
  echo "error: rules directory not found: ${rules_dir}" >&2
  exit 1
fi

check_no_rule_imports() {
  local import_pattern
  local violations=() line

  import_pattern='^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+(all[[:space:]]+)?Cpc\.Proofs\.Rules\.'

  if command -v rg >/dev/null 2>&1; then
    while IFS= read -r line; do violations+=("${line}"); done < <(
      rg -n "${import_pattern}" "${rules_dir}"/*.lean || true
    )
  else
    while IFS= read -r line; do violations+=("${line}"); done < <(
      grep -nHE "${import_pattern}" "${rules_dir}"/*.lean || true
    )
  fi

  if [ "${#violations[@]}" -ne 0 ]; then
    echo "error: top-level CPC rule files must not import other rule files:" >&2
    printf '  %s\n' "${violations[@]}" >&2
    echo "Move shared declarations to Cpc/Proofs/RuleSupport and import that module instead." >&2
    return 1
  fi
}

check_no_rule_imports

echo "Rule style checks passed."
