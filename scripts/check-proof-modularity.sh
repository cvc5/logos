#!/usr/bin/env bash
#
# Modularity invariants of the checker layer, checked textually.
#
# These hold today and each one has drifted at least once, so they are checked
# rather than documented.  Nothing here builds anything: it is a grep pass over
# a dozen files and runs in well under a second.
#
# Each check below says what it is for and what went wrong when it was absent.

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

fail=0
note() { printf '  %s\n' "$*"; }
bad()  { printf '  FAIL: %s\n' "$*" >&2; fail=1; }

# The hand-written checker layer, in dependency order.  A file added to the
# layer belongs in this list.
core_files() {
  local pkg="$1"
  printf '%s\n' \
    "${pkg}/Proofs/Common.lean" \
    "${pkg}/Proofs/Assumptions.lean" \
    "${pkg}/Proofs/RuleSupport/Contract.lean" \
    "${pkg}/Proofs/CheckerState.lean" \
    "${pkg}/Proofs/Invariants/Stability.lean" \
    "${pkg}/Proofs/CheckerCore.lean" \
    "${pkg}/Proofs/Checker.lean"
}

# The files Cpc and CpcMini are meant to hold in common, each of which is one
# file modulo the package name.  Every one of them was forked at some point and
# unforked deliberately; this is what keeps them from re-forking.
#
#   Proofs/Checker.lean                    the soundness proof.  Diverged by 376
#                                          lines before being unforked, because
#                                          CpcMini did not need one invariant.
#   Proofs/CheckerState.lean               the state machine.  Diverged by 145
#                                          lines, because Cpc delegated to
#                                          Proofs/Common.lean where CpcMini
#                                          inlined the same proofs, and because
#                                          CpcMini named generated equation-lemma
#                                          arms by number (see check 6).
#   Proofs/TypePreservation/Datatypes.lean semantics-layer proofs that turned out
#   Proofs/TypePreservation/Nonvacuity.lean   not to vary with the signature at
#   Proofs/TypePreservation/Predicates.lean   all.  They are here so that the set
#   Proofs/Canonical/TypeDefaultBasic.lean    of files a second checker could
#                                          inherit is measured rather than
#                                          assumed.
SHARED_FILES=(
  "Proofs/Checker.lean"
  "Proofs/CheckerState.lean"
  "Proofs/TypePreservation/Datatypes.lean"
  "Proofs/TypePreservation/Nonvacuity.lean"
  "Proofs/TypePreservation/Predicates.lean"
  "Proofs/Canonical/TypeDefaultBasic.lean"
)

# 1. Those files are the same file in both packages.
echo "Checking that Cpc and CpcMini share one copy of each common file..."
for f in "${SHARED_FILES[@]}"; do
  if [ ! -f "Cpc/${f}" ] || [ ! -f "CpcMini/${f}" ]; then
    bad "${f} is missing from one of the packages; it is meant to be in both."
    continue
  fi
  if diff -q \
       <(sed 's/\bCpcMini\./@PKG@./g' "CpcMini/${f}") \
       <(sed 's/\bCpc\./@PKG@./g' "Cpc/${f}") >/dev/null; then
    note "${f}"
  else
    bad "Cpc/${f} and CpcMini/${f} have diverged."
    bad "They are meant to be one file modulo the package name. Diff them with:"
    bad "  diff <(sed 's/\\bCpcMini\\./@PKG@./g' CpcMini/${f}) \\"
    bad "       <(sed 's/\\bCpc\\./@PKG@./g' Cpc/${f})"
  fi
done

# 2. The soundness proof names no rule and no operator.
#
# It is stated about a calculus it does not mention: adding a rule to the
# calculus must not require editing it.
echo "Checking that Checker.lean is calculus-agnostic..."
for pkg in Cpc CpcMini; do
  f="${pkg}/Proofs/Checker.lean"
  n=$(grep -c 'CRule\.' "${f}" || true)
  [ "${n}" = "0" ] || bad "${f} names ${n} CRule constructor(s); it must name none."
  n=$(grep -c 'UserOp' "${f}" || true)
  [ "${n}" = "0" ] || bad "${f} names ${n} UserOp(s); it must name none."
  n=$(grep -c 'AssumptionStability\|assumptionStability\|StableAssumption' "${f}" || true)
  [ "${n}" = "0" ] || bad "${f} names the stability invariant ${n} time(s). Use the checkerExtraInvariant slot."
done
[ "${fail}" = "0" ] && note "Checker.lean names no rule, no operator, no calculus-specific invariant."

# 3. The state machine names no invariant.
#
# CheckerState.lean is the layer a new checker reuses unchanged; an invariant
# appearing there is a commitment leaking out of CheckerCore.lean.
echo "Checking that CheckerState.lean carries no invariant..."
for pkg in Cpc CpcMini; do
  f="${pkg}/Proofs/CheckerState.lean"
  n=$(grep -c 'Invariant' "${f}" || true)
  [ "${n}" = "0" ] || bad "${f} mentions 'Invariant' ${n} time(s); invariants belong in CheckerCore.lean or Invariants/."
done

# 4. Every file the checker layer is declared to consist of is there.
#
# Checks 5 and 6 read `core_files`, and both read it through a shell pipeline
# that discards what it cannot open: a file renamed or removed from the tree but
# left in the list would narrow them silently, and the operator dependency of a
# file nothing opened is `<none>`. Say which file is missing instead, since the
# list is the only statement anywhere of what the layer is.
echo "Checking that the declared checker layer is all present..."
for pkg in Cpc CpcMini; do
  missing=()
  while IFS= read -r f; do
    [ -f "${f}" ] || missing+=("${f}")
  done < <(core_files "${pkg}")
  if [ "${#missing[@]}" -ne 0 ]; then
    bad "${pkg}: the checker layer names ${#missing[@]} file(s) that are not in the tree:"
    printf '    %s\n' "${missing[@]}" >&2
    bad "  Either restore them or update core_files() in this script; the checks"
    bad "  below read that list and cannot see a file it names wrongly."
  else
    note "${pkg}: all $(core_files "${pkg}" | wc -l | tr -d ' ') files"
  fi
done

# 5. The checker layer depends on exactly one signature symbol.
#
# `and` is irreducible: the checker folds the proof state into an and-chain and
# soundness is stated about it.  `not`, `eq` and `imp` were removed and live in
# Proofs/CommonBoolOps.lean, which the checker does not import.  A new operator
# appearing here is a new requirement on every consumer's signature.
echo "Checking the checker layer's operator dependency..."
for pkg in Cpc CpcMini; do
  # `|| true` so that a file check 4 has already reported missing leaves this
  # check reporting what it read rather than aborting the run before the summary.
  ops=$(grep -ho 'UserOp\.[a-zA-Z_0-9]*' $(core_files "${pkg}") 2>/dev/null \
          | sort -u | sed 's/UserOp\.//' | tr '\n' ' ' || true)
  ops="${ops% }"
  if [ "${ops}" = "and" ]; then
    note "${pkg}: and"
  else
    bad "${pkg} checker layer depends on operators: ${ops:-<none>} (expected exactly: and)"
    bad "  A rule-only lemma probably landed in the checker layer; move it to Proofs/CommonBoolOps.lean."
  fi
done

# 6. The checker layer names no arm of a generated definition by number.
#
# `__smtx_typeof.eq_<n>` and `__smtx_model_eval.eq_<n>` are the arm numbering
# the compiler happened to emit for one signature, and it moves when the
# operator set does: the `and` arm of `__smtx_model_eval` is `eq_9` in Cpc and
# `eq_7` in CpcMini.  A checker-layer proof that names a number typechecks
# against one signature and silently means something else against another --
# which is exactly how CheckerState.lean and Common.lean forked.  The arms this
# layer needs are named in Proofs/Common.lean instead.
echo "Checking that the checker layer names no generated arm by number..."
for pkg in Cpc CpcMini; do
  hits=$(grep -Hn '\.eq_[0-9]' $(core_files "${pkg}") 2>/dev/null || true)
  if [ -n "${hits}" ]; then
    bad "${pkg} checker layer names generated equation lemmas by arm number:"
    printf '%s\n' "${hits}" | sed 's/^/    /' >&2
    bad "  Add a named lemma in ${pkg}/Proofs/Common.lean and use that instead."
  else
    note "${pkg}: no arm numbers"
  fi
done

echo
if [ "${fail}" = "0" ]; then
  echo "Checker modularity check passed."
else
  echo "Checker modularity check FAILED. The comments in scripts/check-proof-modularity.sh say what each invariant is for." >&2
  exit 1
fi
