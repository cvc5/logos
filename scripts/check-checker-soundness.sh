#!/usr/bin/env bash
#
# Typecheck the soundness proof without building the rules.
#
# Cpc.Proofs.Checker and Cpc.ApiCorrect are not built by CI: they import
# Proofs/RuleLemmas.lean, which imports all 591 rule files, and that build takes
# over two hours.  So the two files carrying the soundness theorem and its
# restatement about file text are, on their own, unverified by CI.
#
# This closes that gap.  Proofs/RuleLemmas.lean contributes exactly two theorems
# to Checker.lean -- the bridge from what a rule proves to what the checker
# needs.  Stub those two with `sorry` and everything else in both files
# elaborates against the already-built Proofs/CheckerCore, in about a second.
#
# What this does NOT check: the rule proofs themselves, and the generated
# dispatch in RuleLemmas.lean that routes to them.  Those still need the full
# build.  What it does check is every other proof step in Checker.lean and
# ApiCorrect.lean, which is where hand edits land.
#
# The two stubbed signatures are read out of RuleLemmas.lean rather than written
# down here, so that a change to the compiler's template surfaces as a failure
# to find them rather than as a check that silently tests the wrong thing.

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

PKG="${1:-Cpc}"
RULE_LEMMAS="${PKG}/Proofs/RuleLemmas.lean"
CHECKER="${PKG}/Proofs/Checker.lean"
API_CORRECT="${PKG}/ApiCorrect.lean"

for f in "${RULE_LEMMAS}" "${CHECKER}"; do
  [ -f "${f}" ] || { echo "error: ${f} not found." >&2; exit 1; }
done

work="$(mktemp -d "${TMPDIR:-/tmp}/logos-soundness.XXXXXX")"
trap 'rm -rf "${work}"' EXIT
scratch="${work}/SoundnessCheck.lean"

# The signature of a theorem, from its `theorem` line to the `:=` that ends it.
signature_of() {
  awk -v name="$1" '
    $0 ~ "^theorem " name "$" || $0 ~ "^theorem " name "[ (]" { on = 1 }
    on && /^:=$/ { print "  := sorry"; exit }
    on { print }
  ' "${RULE_LEMMAS}"
}

# Everything after a module header, i.e. from the line after the last `open`.
body_of() {
  awk 'BEGIN { last = 0 }
       /^open / { last = NR }
       { line[NR] = $0 }
       END { for (i = last + 1; i <= NR; i++) print line[i] }' "$1"
}

emit_scratch() {
  local canary="$1"
  {
    echo "module"
    echo
    echo "public import ${PKG}.Proofs.CheckerCore"
    echo "import all ${PKG}.Proofs.CheckerCore"
    if [ -f "${API_CORRECT}" ]; then
      echo "public import ${PKG}.ApiChecks"
      echo "import all ${PKG}.ApiChecks"
    fi
    echo
    echo "public section"
    echo
    echo "open Eo"
    echo "open SmtEval"
    echo "open Smtm"
    echo
    echo "set_option linter.unusedVariables false"
    echo "set_option maxHeartbeats 10000000"
    echo
    echo "-- Supplied by ${RULE_LEMMAS}; stubbed so the rules need not be built."
    signature_of cmd_step_proven_facts_of_invariants
    echo
    signature_of cmd_step_pop_proven_facts_of_invariants
    echo
    body_of "${CHECKER}"
    if [ -f "${API_CORRECT}" ]; then
      echo
      body_of "${API_CORRECT}"
    fi
    if [ "${canary}" = "canary" ]; then
      echo
      echo "theorem __soundness_check_canary : False := by exact __no_such_lemma__"
    fi
  } > "${scratch}"
}

# The stubs have to be the two real signatures; an empty or truncated extraction
# would make everything below them fail in confusing ways, or -- worse -- pass.
emit_scratch plain
for name in cmd_step_proven_facts_of_invariants cmd_step_pop_proven_facts_of_invariants; do
  grep -q "^theorem ${name}" "${scratch}" \
    || { echo "error: could not read the signature of ${name} out of ${RULE_LEMMAS}." >&2
         echo "The generated bridge has changed shape; update this script." >&2; exit 1; }
done
[ "$(grep -c '  := sorry' "${scratch}")" = "2" ] \
  || { echo "error: expected exactly 2 stubbed signatures in the scratch module." >&2; exit 1; }

# shellcheck source=lean-toolchain-env.sh
source "${script_dir}/lean-toolchain-env.sh"
logos_configure_lean_toolchain

echo "Building ${PKG}.Proofs.CheckerCore (the soundness proof is checked against it)..."
lake build "${PKG}.Proofs.CheckerCore" >/dev/null

run_lean() {
  lake env lean "${scratch}" 2>&1 | grep -v "declaration uses \`sorry\`" || true
}

echo "Typechecking ${CHECKER}$([ -f "${API_CORRECT}" ] && echo " and ${API_CORRECT}") with the rule bridge stubbed..."
out="$(run_lean)"
if [ -n "${out}" ]; then
  echo "${out}" >&2
  echo >&2
  echo "error: the soundness proof does not typecheck." >&2
  exit 1
fi

# A check that cannot fail is not a check: confirm the harness actually
# elaborates the file by appending a declaration that must be rejected.
echo "Verifying the check is live (canary)..."
emit_scratch canary
if run_lean | grep -q "__no_such_lemma__"; then
  echo
  echo "Soundness typecheck passed (rule proofs not covered; those need the full build)."
else
  echo "error: the canary was not rejected, so this check is not elaborating the file." >&2
  echo "Do not trust a pass from it until this is fixed." >&2
  exit 1
fi
