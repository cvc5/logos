#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/build-all-cpc-rules.sh [options]

Build every CPC proof rule under Cpc/Proofs/Rules and show Lake's verbose
build progress.

By default, rules are built one at a time. Lake still caches shared
dependencies, so rerunning the script resumes from completed work. This avoids
keeping several memory-hungry Lean compiler processes resident simultaneously.

Use --batch-size to trade memory for speed. --all-at-once restores the old,
maximum-parallelism behavior and can require a large amount of RAM.

Options:
  -bN, --batch-size N  Rule targets per Lake invocation (default: 1).
  -jN, --jobs N        Lake runtime threads per invocation (default: 1).
  --all-at-once        Build every rule in one Lake invocation (high memory).
  --dry-run            Print the planned Lake commands without running them.
  --clean              Run `lake clean` before building all rules.
  --clean-only         Run `lake clean` and exit without building.
  -h, --help           Show this help.

Examples:
  scripts/build-all-cpc-rules.sh
  scripts/build-all-cpc-rules.sh --clean
  scripts/build-all-cpc-rules.sh --batch-size 2
  scripts/build-all-cpc-rules.sh --batch-size 1 -j1
  scripts/build-all-cpc-rules.sh --batch-size 4 --dry-run
  scripts/build-all-cpc-rules.sh --all-at-once
  scripts/build-all-cpc-rules.sh --clean-only
USAGE
}

die() {
  echo "error: $*" >&2
  exit 1
}

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"

do_clean=false
build=true
jobs=1
batch_size=1
all_at_once=false
dry_run=false

while [ "$#" -gt 0 ]; do
  case "$1" in
    --clean) do_clean=true ;;
    --clean-only) do_clean=true; build=false ;;
    -b) batch_size="${2:-}"; shift ;;
    -b*) batch_size="${1#-b}" ;;
    --batch-size) batch_size="${2:-}"; shift ;;
    --batch-size=*) batch_size="${1#--batch-size=}" ;;
    -j) jobs="${2:-}"; shift ;;
    -j*) jobs="${1#-j}" ;;
    --jobs) jobs="${2:-}"; shift ;;
    --jobs=*) jobs="${1#--jobs=}" ;;
    --all-at-once) all_at_once=true ;;
    --dry-run) dry_run=true ;;
    -h|--help) usage; exit 0 ;;
    *) usage >&2; die "unknown argument: $1" ;;
  esac
  shift
done

case "${batch_size}" in
  *[!0-9]*|'') die "invalid batch size: ${batch_size}" ;;
esac
[ "${batch_size}" -gt 0 ] || die "batch size must be greater than zero"

case "${jobs}" in
  *[!0-9]*|'') die "invalid job count: ${jobs}" ;;
esac
[ "${jobs}" -gt 0 ] || die "job count must be greater than zero"
export LEAN_NUM_THREADS="${jobs}"

rules_dir="${repo_root}/Cpc/Proofs/Rules"
[ -d "${rules_dir}" ] || die "rules directory not found: ${rules_dir}"

cd "${repo_root}"

if [ "${do_clean}" = true ]; then
  echo "==> Cleaning build artifacts (lake clean)"
  if [ "${dry_run}" = true ]; then
    echo "lake clean"
  else
    lake clean
  fi
fi

if [ "${build}" != true ]; then
  exit 0
fi

if [ "${dry_run}" != true ]; then
  # shellcheck source=lean-toolchain-env.sh
  source "${script_dir}/lean-toolchain-env.sh"
  logos_configure_lean_toolchain
fi

# Collect every rule module from its source file.
modules=()
while IFS= read -r file; do
  rel_file="${file#"${repo_root}/"}"
  module="${rel_file%.lean}"
  module="${module//\//.}"
  modules+=("${module}")
done < <(find "${rules_dir}" -maxdepth 1 -type f -name '*.lean' | sort)

[ "${#modules[@]}" -gt 0 ] || die "no rule files found under ${rules_dir}"

echo "Rules directory: Cpc/Proofs/Rules"
echo "Rule count: ${#modules[@]}"
if [ "${all_at_once}" = true ]; then
  batch_size="${#modules[@]}"
  echo "Build mode: all at once (high memory)"
else
  echo "Build mode: batches of ${batch_size} rule target(s)"
fi
echo "LEAN_NUM_THREADS: ${jobs}"
echo

run_lake_build() {
  if [ "${dry_run}" = true ]; then
    printf 'lake --verbose --no-ansi build'
    printf ' %q' "$@"
    echo
    return
  fi

  lake --verbose --no-ansi build "$@" 2>&1 | awk '
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
}

rule_count="${#modules[@]}"
batch_count=$(( (rule_count + batch_size - 1) / batch_size ))
batch_number=1

for ((start = 0; start < rule_count; start += batch_size)); do
  batch=("${modules[@]:start:batch_size}")
  echo "==> Rule batch ${batch_number}/${batch_count} (${#batch[@]} target(s))"
  run_lake_build "${batch[@]}"
  batch_number=$((batch_number + 1))
done
