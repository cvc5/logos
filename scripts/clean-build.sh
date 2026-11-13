#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/clean-build.sh

Remove Lake build artifacts from both the checker and verification projects.
USAGE
}

case "${1:-}" in
  "") ;;
  -h|--help) usage; exit 0 ;;
  *) usage >&2; exit 2 ;;
esac

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"

echo "==> Cleaning Lake build artifacts"
cd "${repo_root}"
lake clean
lake -d verification clean
echo "==> Build artifacts cleaned"
