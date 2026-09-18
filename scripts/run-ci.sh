#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

configure_lean_toolchain() {
  # shellcheck source=lean-toolchain-env.sh
  source "${script_dir}/lean-toolchain-env.sh"
  logos_configure_lean_toolchain
}

# Examples that Logos accepts as CPC derivations but whose terms fall outside the
# SMT-LIB fragment that Cpc/SmtModel.lean defines, so that the side conditions of
# correct___eo_is_refutation cannot be discharged for them. The `logos`
# executable reports `incomplete` and exits 2 for these; see the Correctness
# section of README.md.
#
#   test/regress/sexp/test-declare-sort.cpc  declares a sort of arity 1, and the
#   specification has no counterpart for a sort constructor applied to a sort.
incomplete_example() {
  case "$1" in
    test/regress/sexp/test-declare-sort.cpc) return 0 ;;
    *) return 1 ;;
  esac
}

# Run every example in a directory through a checker executable, requiring its
# final nonempty output line and its exit status to match what is expected.
run_examples() {
  local exe="$1" dir="$2" pattern="$3" expected="$4"

  shopt -s nullglob
  local examples=("${dir}"/${pattern})

  if [ "${#examples[@]}" -eq 0 ]; then
    echo "No examples found under ${dir}/." >&2
    exit 1
  fi

  echo "Running ${#examples[@]} examples from ${dir} through ${exe}..."
  local example output result status want want_status
  for example in "${examples[@]}"; do
    echo "::group::${example}"

    want="${expected}"
    want_status=0
    if incomplete_example "${example}"; then
      want="incomplete"
      want_status=2
    fi

    set +e
    output="$(lake exe "${exe}" "${example}" 2>&1)"
    status=$?
    set -e

    printf '%s\n' "${output}"
    if [ "${status}" -ne "${want_status}" ]; then
      echo "Expected ${example} to exit with status ${want_status}, got ${status}" >&2
      exit 1
    fi
    result="$(printf '%s\n' "${output}" | awk 'NF { line = $0 } END { print line }')"
    if [ "${result}" != "${want}" ]; then
      echo "Expected ${example} to report ${want}, got: ${result}" >&2
      exit 1
    fi
    echo "::endgroup::"
  done
}

run_proof_hygiene() {
  echo "Checking Cpc and CpcMini for proof escape hatches..."
  bash scripts/check-proof-hygiene.sh
}

# Modularity invariants of the checker layer: that the two packages share one
# Checker.lean, that it names no rule and no operator, and that the layer
# depends on `and` alone. Textual, so it needs no toolchain and no build.
#
# The rule layer's one structural invariant rides along here, for the same
# reason: a rule file importing another rule file makes the two a unit, and
# check-rule-style.sh is textual and just as cheap.
run_proof_modularity() {
  bash scripts/check-proof-modularity.sh
  echo
  bash scripts/check-rule-style.sh
}

# The generated packages against the signature they came from, which this
# repository keeps a copy of. Needs the Eunoia compiler and nothing from cvc5;
# pass "skip" to pass silently where the compiler has not been set up, which is
# what running every group locally wants.
run_regeneration() {
  if [ ! -f install/deps/eoc-env.sh ]; then
    if [ "${1:-}" = "skip" ]; then
      echo "Skipping the regeneration check: install/deps/eoc-env.sh is not"
      echo "there, so the Eunoia compiler has not been set up. Run"
      echo "install/get-eo-compiler.sh once to include this check."
      return 0
    fi
    echo "The Eunoia compiler has not been set up: install/deps/eoc-env.sh" >&2
    echo "is not there. Run install/get-eo-compiler.sh first." >&2
    exit 1
  fi

  echo "Checking that Cpc and CpcMini are what install/defs/Cpc.cached.eo compiles to..."
  if bash install/install-cpc.sh --all --cached --check; then
    return 0
  fi
  cat >&2 <<MSG

A generated package is not what install/defs/Cpc.cached.eo compiles to, so it no
longer follows the signature it comes from. Either it was edited by hand where
it is generated, or it was regenerated from a signature that was never
recorded.

Regenerate both packages from the cached signature with

  install/install-cpc.sh --all --cached

or, if the signature has moved on and the packages should follow it, compile
that one instead, which records it as it goes:

  install/install-cpc.sh --all <cvc5>/proofs/eo/cpc/Cpc.eo
MSG
  exit 1
}

run_regressions() {
  echo "Checking the generated parser tables against the signature..."
  python3 scripts/check-parser-tables.py

  echo "Checking parser tests..."
  lake build Logos.Parser Cpc.Parser
  lake env lean test/Parser.lean
  lake env lean test/CpcParser.lean

  echo "Checking checker diagnostics..."
  lake build Cpc.Diagnostics
  lake env lean test/CheckerDiagnostics.lean

  echo "Building the CPC executables..."
  lake build logos logos-native

  echo "Checking the Lean-native API..."
  lake env lean test/NativeApi.lean

  # Proofs in the Lean term syntax, checked by logos-native.
  run_examples logos-native test/regress '*.cpc.lean' true
  # The same proofs in s-expression syntax, checked by logos (Cpc.Parser).
  run_examples logos test/regress/sexp '*.cpc' correct
}

run_cpc_proofs() {
  local targets=(
    Cpc.Spec
    Cpc.ApiChecks
    Cpc.Proofs.Rules.Refl
    Cpc.Proofs.Rules.Contra
    Cpc.Proofs.Rules.Trans
    Cpc.Proofs.TypePreservation.Nonvacuity
  )

  echo "Compiling representative Cpc proof targets..."
  lake build "${targets[@]}"

  # Cpc.Proofs.Checker and Cpc.ApiCorrect are excluded below because they need
  # all 591 rule files. This typechecks both with the rule bridge stubbed, so
  # the soundness theorem is not left entirely unchecked by CI.
  echo
  bash scripts/check-checker-soundness.sh Cpc

  # Expensive and not currently used in CI checks:
  # Cpc.Proofs.Rules.Chain_resolution
  # Cpc.Proofs.Checker
  # Cpc.ApiCorrect  (correctness of the executable; imports Cpc.Proofs.Checker)
}

run_cpcmini() {
  local targets=(
    CpcMini.Proofs.Checker
    CpcMini.Proofs.TypePreservation.Nonvacuity
  )

  echo "Compiling the CpcMini proofs..."
  lake build "${targets[@]}"
}

group="${1:-all}"
case "${group}" in
  regressions)
    configure_lean_toolchain
    run_regressions
    ;;
  cpc-proofs)
    configure_lean_toolchain
    run_cpc_proofs
    ;;
  cpcmini)
    configure_lean_toolchain
    run_cpcmini
    ;;
  proof-hygiene)
    run_proof_hygiene
    ;;
  proof-modularity)
    run_proof_modularity
    ;;
  regeneration)
    run_regeneration
    ;;
  all)
    run_proof_hygiene
    run_proof_modularity
    run_regeneration skip
    configure_lean_toolchain
    run_regressions
    run_cpc_proofs
    run_cpcmini
    ;;
  *)
    echo "Usage: $0 [all|regressions|cpc-proofs|cpcmini|proof-hygiene|proof-modularity|regeneration]" >&2
    exit 2
    ;;
esac

echo "CI group '${group}' passed."
