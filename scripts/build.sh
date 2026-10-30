#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/build.sh [LAKE-BUILD-OPTION|TARGET]...

Build Logos with the pinned Lean toolchain. If Lean's bundled Clang/LLVM cannot
run on an older Linux host, use compatible host tools automatically.

Examples:
  scripts/build.sh logos
  scripts/build.sh Logos.Parser Cpc.Parser
  scripts/build.sh Cpc.ApiCorrect  # uses the verification project
USAGE
}

case "${1:-}" in
  -h|--help) usage; exit 0 ;;
esac

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

# shellcheck source=lean-toolchain-env.sh
source "${script_dir}/lean-toolchain-env.sh"
logos_configure_lean_toolchain

# Preserve the usual target spelling while selecting the dependency boundary.
# The verification workspace can also build checker targets through its path
# dependency; the checker workspace never loads verification dependencies.
for target in "$@"; do
  case "${target#+}" in
    Cpc.Proofs.*|CpcMini.Proofs.*|Cpc.SmtModel*|CpcMini.SmtModel*|Cpc.SmtValueOrder*|CpcMini.SmtValueOrder*|Cpc.Spec*|CpcMini.Spec*|Cpc.ApiChecks*|Cpc.ApiCorrect*|Cpc.Native.Correct*|CpcVerification|CpcMiniVerification)
      exec lake -d verification build "$@"
      ;;
  esac
done
exec lake build "$@"
