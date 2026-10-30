#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/build-cpc-rule.sh [-jN] <rule>

Build a single CPC proof rule and show Lake's verbose build progress.

Lake already builds a rule's dependencies in parallel across all cores. This
Lake version has no -j/--jobs flag, so -jN here instead caps Lean's program-wide
thread pool via LEAN_NUM_THREADS (use it to limit, not raise, parallelism).
Omit it to use all cores.

Options:
  -jN, --jobs N   Set LEAN_NUM_THREADS=N for this build.

Examples:
  scripts/build-cpc-rule.sh str_in_re_eval
  scripts/build-cpc-rule.sh -j8 str.in_re.eval
  scripts/build-cpc-rule.sh Str_in_re_eval
  scripts/build-cpc-rule.sh Cpc.Proofs.Rules.Str_in_re_eval
  scripts/build-cpc-rule.sh Cpc/Proofs/Rules/Str_in_re_eval.lean
USAGE
}

die() {
  echo "error: $*" >&2
  exit 1
}

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"

jobs=""
args=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    -j) jobs="${2:-}"; shift ;;
    -j*) jobs="${1#-j}" ;;
    --jobs) jobs="${2:-}"; shift ;;
    --jobs=*) jobs="${1#--jobs=}" ;;
    *) args+=("$1") ;;
  esac
  shift
done

if [ -n "${jobs}" ]; then
  case "${jobs}" in
    *[!0-9]*|'') die "invalid job count: ${jobs}" ;;
  esac
  export LEAN_NUM_THREADS="${jobs}"
fi

if [ "${#args[@]}" -ne 1 ]; then
  usage >&2
  exit 2
fi

input="${args[0]#+}"
module=""
rel_file=""

if [[ "${input}" == *.lean ]]; then
  case "${input}" in
    /*) file="${input}" ;;
    *) file="${repo_root}/${input#./}" ;;
  esac

  case "${file}" in
    "${repo_root}"/*) ;;
    *) die "rule file must be inside ${repo_root}" ;;
  esac

  rel_file="${file#"${repo_root}/"}"
  module="${rel_file%.lean}"
  module="${module//\//.}"
elif [[ "${input}" == Cpc.Proofs.Rules.* ]]; then
  module="${input}"
  rel_file="${module//./\/}.lean"
elif [[ "${input}" == Cpc.* || "${input}" == CpcMini.* ]]; then
  module="${input}"
  rel_file="${module//./\/}.lean"
else
  rule="${input//-/_}"
  rule="${rule//./_}"
  first="${rule:0:1}"
  rest="${rule:1}"
  rule_module="$(printf '%s' "${first}" | tr '[:lower:]' '[:upper:]')${rest}"
  module="Cpc.Proofs.Rules.${rule_module}"
  rel_file="Cpc/Proofs/Rules/${rule_module}.lean"
fi

if [ ! -f "${repo_root}/${rel_file}" ]; then
  echo "error: unknown CPC rule: ${args[0]}" >&2
  echo "expected file: ${rel_file}" >&2

  needle="$(basename "${input%.lean}")"
  needle="${needle//-/_}"
  needle="${needle//./_}"
  echo >&2
  echo "close matches:" >&2
  find "${repo_root}/Cpc/Proofs/Rules" \
    -maxdepth 1 \
    -type f \
    -iname "*${needle}*.lean" \
    -print \
    | sed "s#^${repo_root}/##" \
    | sort \
    | head -10 >&2
  exit 1
fi

echo "Rule file: ${rel_file}"
echo "Lake target: ${module}"
echo

cd "${repo_root}"

# shellcheck source=lean-toolchain-env.sh
source "${script_dir}/lean-toolchain-env.sh"
logos_configure_lean_toolchain

lake -d verification --verbose --no-ansi build "${module}" 2>&1 | awk '
  {
    line = $0

    if (match(line, /\[[0-9]+\/[0-9]+\][[:space:]]+(Building|Compiling|Built|Replayed)[[:space:]]+Cpc[^[:space:]]*/)) {
      progress = substr(line, RSTART, RLENGTH)
      split(progress, parts, /[[:space:]]+/)

      step = parts[1]
      status = parts[2]
      target = parts[3]

      file = target
      gsub(/\./, "/", file)
      file = file ".lean"

      if (status == "Building" || status == "Compiling") {
        label = "compiling"
      } else {
        label = tolower(status)
      }

      annotation = step " " label " " file
      if (annotation != last_annotation) {
        print "==> " annotation
        last_annotation = annotation
      }
    }

    if (line ~ /^trace: \.> /) {
      fflush()
      next
    }

    print line
    fflush()
  }
'
