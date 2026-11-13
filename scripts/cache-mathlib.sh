#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

# shellcheck source=lean-toolchain-env.sh
source "${script_dir}/lean-toolchain-env.sh"
logos_configure_lean_toolchain

# Direct Mathlib imports in Cpc/SmtReal.lean, CpcMini/SmtReal.lean, and
# Cpc/Proofs/RealBridge.lean. Fetching also includes their transitive imports.
# Keep this list in sync when adding Mathlib imports; CI's dependency-cache key
# includes this script so those changes fetch and save a fresh cache.
lake -d verification exe cache get \
  Mathlib.Algebra.Order.Archimedean.Real.Basic \
  Mathlib.Data.Rat.Floor \
  Mathlib.Tactic.Ring \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.Positivity
