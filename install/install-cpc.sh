#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: install/install-cpc.sh [OPTION]... [SIGNATURE.eo]

Regenerate Cpc, the package this repository compiles from a Eunoia signature:

  install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo

The run also records that signature in install/defs, which --cached then
compiles in place of naming one:

  install/install-cpc.sh --cached

CpcMini, the reduced package of the same calculus, is left alone by a plain
run. Both packages are checked in and both follow the signature, so a change
that moves Cpc has to move it too, which is what --all is for:

  install/install-cpc.sh --all --cached

Less commonly, what the package is compiled *to* is what is being changed
rather than the calculus it is of. What each symbol of the signature means
is install/defs/Cpc.eos, and what the SMT-LIB symbols it is written against
mean is a configuration the compiler ships; either can be named:

  install/install-cpc.sh --cached --semantics ~/Cpc.eos
  install/install-cpc.sh --cached --smt-semantics ~/smt.eos

A run that names one regenerates against a semantics other than the pair the
checked-in packages are of, so it is for trying a change to the semantics out
rather than for a normal update.

Options:
  --cached             compile the recorded copy of the signature
  --all                regenerate CpcMini as well as Cpc
  --mini               regenerate CpcMini instead of Cpc
  --check              install nothing; report whether the package this run
                       would write and the cached signature it would record
                       are already up to date
  --ethos PATH         an ethos source tree to compile with
  --semantics PATH     what the symbols of the signature mean
                       (default: install/defs/Cpc.eos)
  --smt-semantics PATH what the symbols of SMT-LIB those are written against
                       mean (default: the one the compiler ships)
  -h, --help           show this message

Anything else is handed to install-sig.sh, which this runs once per package;
see install/install-sig.sh --help. --package is refused, since which packages
this writes is what --all and --mini say.

This exits 0 when it did what it was asked and 1 when it did not, and nothing
else. Under --check that is 0 when every package it looked at is up to date and
1 when one of them is not -- including when it is not because the signature
failed to compile. Which of those happened is in the output, never in the
status.
USAGE
}

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
INSTALL_SIG="${script_dir}/install-sig.sh"
[ -f "${INSTALL_SIG}" ] || { echo "error: ${INSTALL_SIG} not found." >&2; exit 1; }

CHECK=0
SIGNATURE=""
# What a run with neither --all nor --mini writes. Cpc alone: CpcMini is a
# reduced copy of the same calculus that most updates have no reason to touch,
# and compiling it costs as much as compiling Cpc.
PACKAGES="Cpc"
want_signature=0
want_value=0
# Everything to hand on to install-sig.sh, which is everything except the two
# options that are this script's own. Which package a run is of is said there
# by --mini or by its absence, once per run, rather than passed through.
declare -a forward=()
for arg in "$@"; do
  if [ "${want_signature}" = "1" ]; then
    SIGNATURE="${arg}"
    want_signature=0
    forward+=("${arg}")
    continue
  fi
  # The value of any other option that takes one, stepped over rather than
  # read: this loop is looking for the signature, and a semantics or an ethos
  # tree named as a separate word is not one however it is spelled.
  if [ "${want_value}" = "1" ]; then
    want_value=0
    forward+=("${arg}")
    continue
  fi
  case "${arg}" in
    -h|--help) usage; exit 0 ;;
    --check) CHECK=1 ;;
    --cached) SIGNATURE="the cached signature" ;;
    --signature) want_signature=1 ;;
    --signature=*) SIGNATURE="${arg#*=}" ;;
    --semantics|--smt-semantics|--lean-config|--cache|--ethos|--build-dir|--out-dir|--deps-dir)
      want_value=1 ;;
    --all) PACKAGES="Cpc CpcMini"; continue ;;
    --mini) PACKAGES="CpcMini"; continue ;;
    --package|--package=*)
      echo "error: ${arg} names a package, and which packages this writes is" >&2
      echo "what --all and --mini say. Run install/install-sig.sh for a package" >&2
      echo "of your own." >&2
      exit 1
      ;;
    -*) ;;
    *.eo) SIGNATURE="${arg}" ;;
  esac
  forward+=("${arg}")
done

if [ -z "${SIGNATURE}" ]; then
  echo "error: no signature to compile. Name one, e.g." >&2
  echo "  install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo" >&2
  echo "or compile the copy kept in this repository with --cached." >&2
  exit 1
fi

# The packages of a run, written out as prose rather than as the array bash
# prints with a space for a separator.
list() {
  local out="" item
  for item in "$@"; do
    if [ -z "${out}" ]; then out="${item}"; else out="${out}, ${item}"; fi
  done
  printf '%s' "${out}"
}

# One package, named as this repository spells it. install-sig.sh is told which
# one by --mini or by nothing at all, so that is the only difference here.
run_package() {
  if [ "$1" = "CpcMini" ]; then
    bash "${INSTALL_SIG}" --brief "${forward[@]}" --mini
  else
    bash "${INSTALL_SIG}" --brief "${forward[@]}"
  fi
}

# Every package this run is of is checked, whatever an earlier one did, so that
# one failure does not hide another package's verdict. A run that did not get
# as far as a verdict -- a signature the compiler rejects, a missing ethos tree
# -- counts here as the package not being up to date, since what it establishes
# is that the package cannot be shown to be. The two are not separate exit
# statuses: the run that failed said why, above, and a caller that needs to
# know reads that rather than a number.
if [ "${CHECK}" = "1" ]; then
  declare -a current=()
  declare -a stale=()
  first=1
  for pkg in ${PACKAGES}; do
    [ "${first}" = "1" ] || echo
    first=0
    if run_package "${pkg}"; then
      current+=("${pkg}")
    else
      stale+=("${pkg}")
    fi
  done

  echo
  if [ "${#stale[@]}" -eq 0 ]; then
    echo "==> Up to date with ${SIGNATURE}: $(list "${current[@]}")."
    echo "Nothing was written."
    exit 0
  fi
  echo "==> Could not be shown up to date with ${SIGNATURE}: $(list "${stale[@]}")."
  if [ "${#current[@]}" -gt 0 ]; then
    echo "Up to date: $(list "${current[@]}")."
  fi
  echo "Nothing was written. Where the run above compiled the signature and"
  echo "found a difference, rerun without --check to apply it; where it failed"
  echo "to compile the signature, that is what to fix first."
  exit 1
fi

# The rule files this run's packages hold, named as this repository spells
# them. A rule file is written only for a rule that has none -- one that exists
# is preserved, since that is where its proof lives -- so a file here
# afterwards that was not here before is a rule the calculus has just gained,
# and the only kind of file carrying `sorry`. Reading the directory rather than
# the runs' output is what lets this say so: they are installed with --brief.
repo_root="$(cd "${script_dir}/.." && pwd)"

rules_snapshot() {
  local pkg file
  shopt -s nullglob
  for pkg in ${PACKAGES}; do
    for file in "${repo_root}/${pkg}/Proofs/Rules"/*.lean; do
      echo "${pkg}/Proofs/Rules/${file##*/}"
    done
  done
  shopt -u nullglob
}

rules_before="$(mktemp "${TMPDIR:-/tmp}/install-cpc-rules.XXXXXX")"
rules_after="$(mktemp "${TMPDIR:-/tmp}/install-cpc-rules.XXXXXX")"
trap 'rm -f "${rules_before}" "${rules_after}"' EXIT
rules_snapshot | LC_ALL=C sort > "${rules_before}"

# An install, where a later run has no business starting if an earlier one did
# not finish. The status is flattened to 1 as everywhere else here: install-sig
# tells apart a usage mistake from a failed compile and this does not, so it
# passes on that it failed and leaves that run's own output to say how.
first=1
for pkg in ${PACKAGES}; do
  [ "${first}" = "1" ] || echo
  first=0
  run_package "${pkg}" || exit 1
done

rules_snapshot | LC_ALL=C sort > "${rules_after}"
declare -a new_rules=()
while IFS= read -r rule; do
  new_rules+=("${rule}")
done < <(comm -13 "${rules_before}" "${rules_after}")

cat <<DONE

==> Done. ${PACKAGES// /, } regenerated from ${SIGNATURE}.

Build with:

  scripts/build.sh ${PACKAGES}

A preserved rule file whose statement the calculus has changed will fail to
build. Review with git diff before committing.
DONE

# A plain run leaves CpcMini on whatever signature it was last compiled from,
# which the regeneration check holds to the cached one. Said here rather than
# left to that check to report later.
if [ "${PACKAGES}" = "Cpc" ]; then
  cat <<'MINI'

CpcMini was not regenerated: a plain run is of Cpc alone. Where this change
moves what the signature compiles to, rerun with --all so that both packages
follow it.
MINI
fi

# Said only when there is something to say it about: a run that adds no rule
# has written no stub, and a standing note about `sorry` in that case sends a
# reader looking for one that is not there.
if [ "${#new_rules[@]}" -gt 0 ]; then
  echo
  echo "==> ${#new_rules[@]} new rule file(s), each with \`sorry\` for a proof:"
  echo
  # A run that finds Rules/ empty writes one file per rule of the calculus,
  # which is a list nobody reads. Say how many are not shown rather than
  # print all of them.
  shown=0
  for rule in "${new_rules[@]}"; do
    if [ "${shown}" -ge 20 ]; then
      echo "  ... and $(( ${#new_rules[@]} - shown )) more (git status lists them all)"
      break
    fi
    echo "  ${rule}"
    shown=$((shown + 1))
  done
fi
