#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: install/install-sig.sh [OPTION]... [SIGNATURE.eo]

Compile a Eunoia signature with ethos-eoc and install the Lean files it
generates into a package of this repository, by default Cpc.

What is generated is the signature-wide part of the package: the checker, the
term and operator datatypes, the parser configuration, the SMT-LIB semantics
modules, the spec, the rule lemmas, and one file per proof rule. What is
hand-written -- everything under Proofs/ other than RuleLemmas.lean and
Rules/, and the Api and Diagnostics modules -- is left alone.

Each of those signature-wide modules is installed with a banner saying it is
auto-generated, that an install overwrites it, and where the semantics it
realizes are written down: docs/smt-model-definitions.pdf. Rule files do not
get one, since a rule file is where a proof then goes.

Existing files under Proofs/Rules/ are preserved, since those are where the
proofs of this repository live and the compiler only ever emits a statement
with `sorry` for a body. A rule that has no file yet gets that stub, which is
what makes a newly added rule of the calculus visible here as an obligation.
To see what the compiler emits for a rule that has one, delete its file and
install again.

The signature to compile is named with --signature, or as a bare path ending
in .eo, which is the same thing:

  install/install-sig.sh ~/cvc5/proofs/eo/cpc/Cpc.eo

It is not something install/get-eo-compiler.sh fetches, so any signature
reachable on this machine -- a cvc5 checkout, or one being worked on locally --
can be compiled without downloading anything.

A copy of the signature the packages here were last compiled from is kept in
this repository as a single file, install/defs/Cpc.cached.eo, with every
(include ...) of the original spliced in and its comments dropped. --cached
compiles that copy, which is how the packages can be regenerated, and checked,
without a cvc5 checkout at all; it is what CI does.

An install of Cpc or CpcMini rewrites that copy itself, so the two cannot
drift: what a full run compiled is what gets recorded. An install that selects
rules with --rules compiles a reduced calculus, and one into another package
says nothing about these two, so neither records anything and both say so.

The compiler comes from install/deps/eoc-env.sh, which
install/get-eo-compiler.sh writes, unless --ethos names another ethos tree.

Options:
  --signature PATH     the Eunoia signature to compile, e.g.
                       <cvc5>/proofs/eo/cpc/Cpc.eo. A bare path ending in .eo
                       means the same and needs no option name, as long as it
                       does not follow --rules, which reads every word after
                       it as a rule. Required unless --cached names the copy
                       kept here instead
  --ethos PATH         an ethos source tree containing tools/eoc/driver.py
                       (default: the one install/deps/eoc-env.sh records).
                       Also redirects --build-dir to that tree, so a local
                       checkout is never mixed with install/deps/
  --cached             compile the copy of the signature kept in this
                       repository instead of naming one with --signature
  --brief              say what this run did and leave what it means to
                       whatever ran it, which is what install-cpc.sh does with
                       the two runs it makes
  --cache PATH         where that copy lives
                       (default: <install>/defs/Cpc.cached.eo)
  --package NAME       the package under this repository to install into
                       (default: Cpc)
  --mini               the reduced package: --package CpcMini, the five rules
                       below unless --rules gives others, no parser, and
                       `partial def` rewritten to `def`
  --rules RULE...      compile only these rules; everything up to the next
                       option is taken as a rule name
                       (default: the whole signature)
  --check              do not install anything: compile, compare against the
                       package, and exit 0 only if it is already up to date,
                       1 if an install would change it. Every other option
                       means the same under --check as without it
  --semantics PATH     what the symbols of the signature mean, as a
                       configuration the compiler compiles before it runs
                       (default: <install>/defs/Cpc.eos)
  --smt-semantics PATH the same for the SMT-LIB semantics that one is written
                       against: what a symbol of SMT-LIB means to a model,
                       which is the target of the compilation rather than
                       anything about this signature. The compiler ships one
                       and compiles it where this names none, so naming one
                       is changing what the target means
                       (default: <ethos>/tools/eoc/semantics/smt.eos)
  --lean-config PATH   why each recursive program of the input terminates,
                       read by the lean-meta stage. The compiler writes one
                       from --semantics and gives it to that stage itself, so
                       naming one is rarely wanted
  --build-dir DIR      the ethos-eoc build tree
  --out-dir DIR        where to stage what the compiler publishes before it is
                       installed (default: <deps>/eoc-out)
  --deps-dir DIR       where eoc-env.sh is (default: <install>/deps)
  -h, --help           show this message

Examples:
  install/install-sig.sh ~/cvc5/proofs/eo/cpc/Cpc.eo
  install/install-sig.sh --cached
  install/install-sig.sh --cached --check
  install/install-sig.sh --signature ~/cvc5/proofs/eo/cpc/Cpc.eo --mini
  install/install-sig.sh ~/sig.eo --package Mine --rules symm refl trans
  install/install-sig.sh --cached --smt-semantics ~/smt.eos
USAGE
}

# A leading ~ in --option=VALUE is not the shell's to expand: it does that at
# the start of a word, and there the word starts with --option. So the tilde
# arrives here as a character, and every option that takes a path expands it
# the way the shell would have. ~user is left alone, since resolving that needs
# more than $HOME.
expand_tilde() {
  case "$1" in
    "~") printf '%s\n' "${HOME}" ;;
    "~/"*) printf '%s\n' "${HOME}/${1#\~/}" ;;
    *) printf '%s\n' "$1" ;;
  esac
}

SIGNATURE=""
CACHED=0
BRIEF=0
CACHE_FILE=""
ETHOS_DIR=""
ETHOS_GIVEN=0
PACKAGE=""
MINI=0
declare -a RULES=()
RULES_GIVEN=0
NO_PARSER=0
NO_PARTIAL=0
CHECK=0
SEMANTICS=""
SMT_SEMANTICS=""
LEAN_CONFIG=""
BUILD_DIR=""
OUT_DIR=""
DEPS_DIR=""

while [ $# -gt 0 ]; do
  case "$1" in
    --signature) SIGNATURE="${2:?--signature requires a value}"; shift 2 ;;
    --signature=*) SIGNATURE="${1#*=}"; shift ;;
    --cached) CACHED=1; shift ;;
    --brief) BRIEF=1; shift ;;
    --cache) CACHE_FILE="${2:?--cache requires a value}"; shift 2 ;;
    --cache=*) CACHE_FILE="${1#*=}"; shift ;;
    --ethos) ETHOS_DIR="${2:?--ethos requires a value}"; ETHOS_GIVEN=1; shift 2 ;;
    --ethos=*) ETHOS_DIR="${1#*=}"; ETHOS_GIVEN=1; shift ;;
    --package) PACKAGE="${2:?--package requires a value}"; shift 2 ;;
    --package=*) PACKAGE="${1#*=}"; shift ;;
    --mini) MINI=1; shift ;;
    --rules)
      shift
      RULES_GIVEN=1
      while [ $# -gt 0 ] && [ "${1#-}" = "$1" ]; do
        RULES+=("$1")
        shift
      done
      ;;
    --check) CHECK=1; shift ;;
    --semantics) SEMANTICS="${2:?--semantics requires a value}"; shift 2 ;;
    --semantics=*) SEMANTICS="${1#*=}"; shift ;;
    --smt-semantics) SMT_SEMANTICS="${2:?--smt-semantics requires a value}"; shift 2 ;;
    --smt-semantics=*) SMT_SEMANTICS="${1#*=}"; shift ;;
    --lean-config) LEAN_CONFIG="${2:?--lean-config requires a value}"; shift 2 ;;
    --lean-config=*) LEAN_CONFIG="${1#*=}"; shift ;;
    --build-dir) BUILD_DIR="${2:?--build-dir requires a value}"; shift 2 ;;
    --build-dir=*) BUILD_DIR="${1#*=}"; shift ;;
    --out-dir) OUT_DIR="${2:?--out-dir requires a value}"; shift 2 ;;
    --out-dir=*) OUT_DIR="${1#*=}"; shift ;;
    --deps-dir) DEPS_DIR="${2:?--deps-dir requires a value}"; shift 2 ;;
    --deps-dir=*) DEPS_DIR="${1#*=}"; shift ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "unrecognized option $1" >&2; usage >&2; exit 2 ;;
    # A bare path ending in .eo is the signature. Anything else that is not an
    # option is named as the mistake it is rather than guessed at, so that a
    # mistyped path is not read as a rule or a package.
    *.eo)
      if [ -n "${SIGNATURE}" ]; then
        echo "error: two signatures given: ${SIGNATURE} and $1." >&2
        exit 2
      fi
      SIGNATURE="$1"
      shift
      ;;
    *)
      echo "error: $1 is neither an option nor a signature." >&2
      echo "A signature is a path ending in .eo. See --help." >&2
      exit 2
      ;;
  esac
done

# --mini selects rules of its own further down, so whether this run was asked
# to compile a reduced calculus is a question about the command line and has to
# be answered while that is still what RULES_GIVEN says.
RULES_ASKED_FOR="${RULES_GIVEN}"

# Every option above that takes a path, whether it arrived as --option VALUE or
# as --option=VALUE.
SIGNATURE="$(expand_tilde "${SIGNATURE}")"
CACHE_FILE="$(expand_tilde "${CACHE_FILE}")"
ETHOS_DIR="$(expand_tilde "${ETHOS_DIR}")"
SEMANTICS="$(expand_tilde "${SEMANTICS}")"
SMT_SEMANTICS="$(expand_tilde "${SMT_SEMANTICS}")"
LEAN_CONFIG="$(expand_tilde "${LEAN_CONFIG}")"
BUILD_DIR="$(expand_tilde "${BUILD_DIR}")"
OUT_DIR="$(expand_tilde "${OUT_DIR}")"
DEPS_DIR="$(expand_tilde "${DEPS_DIR}")"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
DEPS_DIR="${DEPS_DIR:-${script_dir}/deps}"
CACHE_FILE="${CACHE_FILE:-${repo_root}/install/defs/Cpc.cached.eo}"

# What get-eo-compiler.sh installed, if it has been run. Anything named on the
# command line wins over it.
ENV_FILE="${DEPS_DIR}/eoc-env.sh"
if [ -f "${ENV_FILE}" ]; then
  # shellcheck source=/dev/null
  source "${ENV_FILE}"
fi

# --ethos names a tree that is not the one install/deps/eoc-env.sh describes,
# so the recorded build directory belongs to another ethos and must not be
# used as a default for it. Deriving it from the named tree instead is what
# keeps a local-checkout run from silently mixing the two:
# the binary under the recorded build dir resolves its templates against the
# tree it was configured from, so a mixed run compiles with the wrong
# templates and still exits 0.
if [ "${ETHOS_GIVEN}" = "1" ]; then
  EOC_BUILD_DIR=""
fi

ETHOS_DIR="${ETHOS_DIR:-${EOC_ETHOS_DIR:-}}"

# Where the signature $1 sits, for the header of the cached copy: the path it
# has inside the checkout it came from, which is the same path in any copy of
# that project, or its name when it is not in one. What is deliberately not
# here is the commit -- see signature_version.
signature_location() {
  local dir sig top
  dir="$(cd "$(dirname "$1")" && pwd)"
  sig="${dir}/$(basename "$1")"
  if top="$(git -C "${dir}" rev-parse --show-toplevel 2>/dev/null)"; then
    printf '%s\n' "${sig#"${top}"/}"
  else
    printf '%s\n' "$(basename "${sig}")"
  fi
}

# The version of the checkout the signature $1 came from, for the terminal and
# not for the file. It is what identifies the signature to a person, but
# writing it into the copy would make the copy depend on which checkout it was
# made from rather than on the calculus: two people flattening the same
# signature from two checkouts would then produce two different files, and an
# install would rewrite a line that says nothing about what it compiles to.
# Empty when there is no checkout to name.
signature_version() {
  local dir sha
  dir="$(cd "$(dirname "$1")" && pwd)"
  git -C "${dir}" rev-parse --show-toplevel >/dev/null 2>&1 || return 0
  sha="$(git -C "${dir}" rev-parse HEAD 2>/dev/null)" || return 0
  if [ -n "$(git -C "${dir}" status --porcelain -- "${dir}" 2>/dev/null)" ]; then
    printf '%s, with uncommitted changes under %s\n' "${sha}" "$(basename "${dir}")"
  else
    printf '%s\n' "${sha}"
  fi
}

# Write the signature $1 to $2 as a single file: every (include "...") replaced
# by the text of the file it names, depth first, each file written only the
# first time it is reached, and every comment dropped. Writing a file once is
# what makes the result equivalent to the original rather than a redeclaration
# of everything the tree shares: ethos also reads a file only the first time it
# is named, see markIncluded in its src/state.cpp. Which lines name a file is
# decided the way driver.py decides it, see INCLUDE_RE and strip_comment there,
# so the copy contains the files a compilation of the original would have read
# and no others.
flatten_signature() {
  python3 - "$1" "$2" "$(signature_location "$1")" <<'PY'
import os
import re
import sys

INCLUDE_RE = re.compile(r'^\(include\s+"([^"]+)"\s*\)')
# Anything else that names another file. Splicing cannot represent it, and
# leaving it in place would resolve it against the copy's own directory, so
# stop instead of writing a file that quietly means something else.
UNSPLICEABLE_RE = re.compile(r"^\((include|reference)\b")

HEADER = """\
; This file is generated by install/install-cpc.sh. Do not edit it.
;
; It is a flattened copy of:
;   %s
;
; Every include is replaced by the contents of the file it names, with each
; file appearing once in Ethos's input order. Source comments are omitted; read
; the original signature for its documentation.
"""


def strip_comments(text):
    """The lines of `text` with every comment removed, and with the lines that
    leaves empty dropped along with the ones that already were.

    A `;` inside a string literal or a |quoted symbol| is content rather than
    the start of a comment, and a line that begins inside either is passed
    through untouched, since its blankness and its trailing spaces are content
    too. `""` is how a string literal spells a quote, so it does not end one.
    """
    lines = []
    line = []
    quote = ""
    quoted_at_start = False
    index = 0
    length = len(text)

    def end_line():
        joined = "".join(line)
        if quoted_at_start or quote:
            lines.append(joined)
        elif joined.strip():
            lines.append(joined.rstrip())

    while index < length:
        char = text[index]
        if char == "\n":
            end_line()
            del line[:]
            quoted_at_start = bool(quote)
            index += 1
            continue
        if not quote:
            if char == ";":
                newline = text.find("\n", index)
                index = length if newline < 0 else newline
                continue
            if char in '"|':
                quote = char
        elif char == quote:
            if char == '"' and text[index + 1 : index + 2] == '"':
                line.append(char)
                index += 1
                char = text[index]
            else:
                quote = ""
        line.append(char)
        index += 1
    end_line()
    if quote:
        sys.exit("error: a %s left open at the end of the file." % quote)
    return lines


source, dest, location = sys.argv[1], sys.argv[2], sys.argv[3]
root = os.path.realpath(source)
base = os.path.dirname(root)
seen = set()
out = []


def name_of(path):
    return os.path.relpath(path, base)


def visit(path, named_by):
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        sys.exit("error: %s includes %s, which is not there." % (named_by, path))
    if real in seen:
        out.append("; (%s is included above)\n" % name_of(real))
        return
    seen.add(real)
    out.append("\n; ==== %s ====\n" % name_of(real))
    with open(real) as handle:
        text = handle.read()
    for line in strip_comments(text):
        command = line.strip()
        match = INCLUDE_RE.match(command)
        if match:
            visit(os.path.join(os.path.dirname(real), match.group(1)), name_of(real))
            continue
        if UNSPLICEABLE_RE.match(command):
            sys.exit("error: %s: cannot splice `%s` into one file." % (name_of(real), command))
        out.append(line + "\n")


visit(root, os.path.basename(root))
with open(dest, "w") as handle:
    handle.write(HEADER % location)
    handle.write("".join(out))
PY
}

# --cached is --signature with the one path this repository keeps filled in.
if [ "${CACHED}" = "1" ]; then
  if [ -n "${SIGNATURE}" ]; then
    echo "error: --cached and ${SIGNATURE} are two different signatures." >&2
    echo "Give one or the other." >&2
    exit 2
  fi
  if [ ! -f "${CACHE_FILE}" ]; then
    echo "error: there is no cached signature at ${CACHE_FILE}." >&2
    echo "An install of Cpc or CpcMini writes one." >&2
    exit 1
  fi
  SIGNATURE="${CACHE_FILE}"
fi

if [ -z "${SIGNATURE}" ]; then
  echo "error: no signature to compile. Name one, e.g." >&2
  echo "  install/install-sig.sh ~/cvc5/proofs/eo/cpc/Cpc.eo" >&2
  echo "or compile the copy kept in this repository with --cached." >&2
  exit 2
fi
[ -f "${SIGNATURE}" ] || { echo "error: signature ${SIGNATURE} not found." >&2; exit 1; }

if [ -z "${ETHOS_DIR}" ]; then
  echo "error: no ethos tree to work from. Run install/get-eo-compiler.sh" >&2
  echo "first, or name one with --ethos. See --help." >&2
  exit 1
fi

DRIVER="${ETHOS_DIR}/tools/eoc/driver.py"
[ -f "${DRIVER}" ] || { echo "error: ${DRIVER} not found." >&2; exit 1; }

# The mini package is the same install with a different name, no parser, no
# `partial`, and a handful of rules.
if [ "${MINI}" = "1" ]; then
  PACKAGE="${PACKAGE:-CpcMini}"
  NO_PARSER=1
  NO_PARTIAL=1
  if [ "${RULES_GIVEN}" = "0" ]; then
    RULES=(symm contra refl scope trans)
    RULES_GIVEN=1
  fi
fi
PACKAGE="${PACKAGE:-Cpc}"

# The semantics are this repository's, not the compiler's: the compiler reads
# the configuration and compiles it, in place of the set it ships with, into
# the two files the model-smt and lean-meta stages read. Where those two come
# out is the compiler's own: a set compiles by the role it is given and not by
# where it stands, and each stage is handed what it reads, so neither file is
# named here. The SMT-LIB semantics they are written against is the
# compiler's too, which is what --smt-semantics replaces.
SEMANTICS="${SEMANTICS:-${script_dir}/defs/Cpc.eos}"
BUILD_DIR="${BUILD_DIR:-${EOC_BUILD_DIR:-${ETHOS_DIR}/build-eoc}}"
OUT_DIR="${OUT_DIR:-${DEPS_DIR}/eoc-out}"
DEST_DIR="${repo_root}/${PACKAGE}"
PACKAGE_DIR="${DEST_DIR}"

# How much of the difference --check prints when it finds one: enough to see
# what kind of difference it is, not so much that a wholesale regeneration
# buries the message that follows it.
DIFF_FILES=3
DIFF_LINES=20

# --check performs the whole install into a throwaway copy of the package and
# then compares, rather than reimplementing what an install would have done.
# Every step below runs unchanged against that copy, so the check cannot drift
# from the install it is checking: a file the install would not touch was
# copied verbatim and compares equal, and whatever differs at the end is
# exactly the set of changes an install would make.
if [ "${CHECK}" = "1" ]; then
  CHECK_DIR="$(mktemp -d "${TMPDIR:-/tmp}/install-cpc-check.XXXXXX")"
  trap 'rm -rf "${CHECK_DIR}"' EXIT INT TERM
  DEST_DIR="${CHECK_DIR}/${PACKAGE}"
  if [ -d "${PACKAGE_DIR}" ]; then
    cp -R "${PACKAGE_DIR}" "${DEST_DIR}"
  fi
fi

[ -f "${SEMANTICS}" ] || {
  echo "error: --semantics file ${SEMANTICS} not found." >&2
  exit 1
}
if [ -n "${SMT_SEMANTICS}" ] && [ ! -f "${SMT_SEMANTICS}" ]; then
  echo "error: --smt-semantics file ${SMT_SEMANTICS} not found." >&2
  exit 1
fi

# The signature-wide files the lean subcommand of driver.py publishes, in
# module dependency order, named as they stand in the package. The driver
# publishes its tree in the layout of the package the tree is installed into,
# see LEAN_OUTPUTS in tools/eoc/driver.py, so one name is both where a file is
# read and where it is written; the per-rule files under Proofs/Rules/ stand
# there too and are handled separately below. This list has to cover
# everything the driver writes apart from those; a file added there but not
# here is silently left behind.
LEAN_OUTPUTS=(
  "Logos.lean"
  "LogosTerm.lean"
  "Parser.lean"
  "SmtEval.lean"
  "SmtModelDefs.lean"
  "SmtValueOrder.lean"
  "SmtModel.lean"
  "Spec.lean"
  "Proofs/RuleLemmas.lean"
)

# The banner every generated file carries, so that a reader who opens one in
# the middle of the package -- or a diff of one -- is told where it came from
# before anything else. It goes ahead of `module`, which Lean allows: comments
# are not commands. The signature it names is the copy this repository keeps
# rather than whatever path this run compiled, since that path is particular to
# the machine it ran on and the copy is what CI compiles.
GENERATED_HEADER='-- This file is auto-generated by install/install-cpc.sh, which compiles the
-- Eunoia signature recorded in install/defs/Cpc.cached.eo into Lean.
-- Do not edit. Change the signature, or the compiler, instead.
--
-- The SMT-LIB semantics and the checker specification that these definitions
-- realize are documented in docs/smt-model-definitions.pdf.'

# Put the banner ahead of a file the compiler just published. Idempotent: a
# file that already carries it is left alone, so that a second pass over an
# installed tree does not stack banners.
prepend_header() {
  local file="$1" tmp
  case "$(head -n 1 "${file}")" in
    "-- This file is auto-generated by install/install-cpc.sh"*) return 0 ;;
  esac
  tmp="${file}.hdr"
  { printf '%s\n\n' "${GENERATED_HEADER}"; cat "${file}"; } > "${tmp}"
  mv "${tmp}" "${file}"
}

# sed -i takes an argument on BSD and not on GNU; giving it a suffix and
# deleting the backup is what both accept.
sed_in_place() {
  sed -i.bak -e "$1" "$2"
  rm -f "$2.bak"
}

# The name of the calculus as the generated files spell it, read off the first
# import of the generated checker. Lean allows an `all` modifier before the
# module name, which is kept out of the captured name.
detect_generated_calc() {
  local logos_file="$1/Logos.lean" import_line
  [ -f "${logos_file}" ] || return 1
  import_line="$(grep -m1 '^import ' "${logos_file}" || true)"
  if [[ "${import_line}" =~ ^import[[:space:]]+(all[[:space:]]+)?([^.]+)\. ]]; then
    printf '%s\n' "${BASH_REMATCH[2]}"
    return 0
  fi
  return 1
}

# The calculus name driver.py derives from a file name, which is the file name
# up to its first dot in upper camel case. Keep in sync with input_base_name
# and lean_calc_name in tools/eoc/driver.py. Only a fallback: the name is read
# out of the generated files when they are there.
calc_name_of() {
  local stem calc="" part head rest
  stem="$(basename "$1")"
  stem="${stem%%.*}"
  for part in $(printf '%s' "${stem}" | tr -cs '[:alnum:]' ' '); do
    # Upper camel case, spelled without ${x^} so that bash 3.2 can run this.
    head="$(printf '%s' "${part}" | cut -c1 | tr '[:lower:]' '[:upper:]')"
    rest="$(printf '%s' "${part}" | cut -c2-)"
    calc+="${head}${rest}"
  done
  [ -n "${calc}" ] || calc="EoCalc"
  [[ "${calc}" =~ ^[[:alpha:]] ]] || calc="Calc${calc}"
  printf '%s\n' "${calc}"
}

echo "==> Compiling ${SIGNATURE}"
echo "    ethos    ${ETHOS_DIR}"
echo "    package  ${PACKAGE_DIR}"
[ -z "${SMT_SEMANTICS}" ] || echo "    smt      ${SMT_SEMANTICS}"

# --semantics is what the symbols of the signature mean and --smt-semantics
# what the SMT-LIB ones they are written against do; the compiler compiles the
# one it ships with where the second names none. --lean-config is left out
# unless it was named, since the compiler writes one from --semantics and
# gives the lean-meta stage that.
driver_args=(lean --build-dir "${BUILD_DIR}" --final-out-dir "${OUT_DIR}"
             --semantics "${SEMANTICS}" --skip-cvc5)
[ -z "${SMT_SEMANTICS}" ] || driver_args+=(--smt-semantics "${SMT_SEMANTICS}")
[ -z "${LEAN_CONFIG}" ] || driver_args+=(--lean-config "${LEAN_CONFIG}")
if [ -x "${BUILD_DIR}/ethos-eoc" ]; then
  driver_args+=(--no-build)
else
  echo "    ethos-eoc is not built yet; building it into ${BUILD_DIR}"
fi
[ "${NO_PARSER}" = "1" ] && driver_args+=(--no-parser)
if [ "${RULES_GIVEN}" = "1" ]; then
  if [ "${#RULES[@]}" -eq 0 ]; then
    echo "error: --rules was given with no rule names. Drop it to compile the" >&2
    echo "whole signature." >&2
    exit 2
  fi
  driver_args+=("${SIGNATURE}" "${RULES[@]}")
else
  driver_args+=(--all "${SIGNATURE}")
fi

python3 "${DRIVER}" "${driver_args[@]}"

LEAN_DIR="${OUT_DIR}/lean"
[ -d "${LEAN_DIR}" ] || { echo "error: the compiler published nothing in ${LEAN_DIR}." >&2; exit 1; }

# What the checker layer requires of a signature, checked against what the
# compiler just emitted rather than against the signature text: the name an
# operator compiles to need not be its spelling, and `:right-assoc-nil` is
# visible only in what it generates. Nothing is installed if this fails, so a
# signature that cannot work is refused before it overwrites a working package
# rather than failing deep inside a Lean build with a confusing error.
#
# The list is one operator plus a conditional. It is short because the checker
# layer was reduced to it -- `not`, `=` and `imp` were requirements once and
# are not now. What each entry is for is in docs/modularity.md, "What a new
# checker supplies".
echo "==> Checking the signature contract"
contract_errors=()

TERM_MODULE="${LEAN_DIR}/LogosTerm.lean"
CORE_MODULE="${LEAN_DIR}/Logos.lean"
SPEC_MODULE="${LEAN_DIR}/Spec.lean"

# 1. An operator named `and`.
#
#    Soundness is stated about the conjunction of a proof's assumptions:
#    `__eo_invoke_assume_list` walks the input problem as a `CArgList`, and
#    `argListAssumes` folds that list -- like `stateAssumes` / `statePushes` /
#    `stateProvens` fold the checker stack -- into the `and`-chain the theorem
#    concludes about. Those name the operator directly.
if [ -f "${TERM_MODULE}" ] && \
   ! grep -qE "^[[:space:]]*\|[[:space:]]+and[[:space:]]*:[[:space:]]*UserOp\b" "${TERM_MODULE}"; then
  contract_errors+=("no operator \`and\`, which the soundness statement is about")
fi

# 2. It means conjunction to the SMT-LIB semantics.
#
#    This is the seam where a mistake would be silent. A signature that
#    declared `and` and translated it to something else would compile, would
#    check proofs, and `correct___eo_is_refutation` would be a statement about
#    the wrong formula. Nothing downstream re-checks it, so it is checked here.
if [ -f "${SPEC_MODULE}" ] && \
   ! grep -qE "UserOp\.and\).*=> *\(?SmtTerm\.and\b" "${SPEC_MODULE}"; then
  contract_errors+=("the semantics does not send \`and\` to SmtTerm.and")
fi

# 3. `:right-assoc-nil true` -- but only where the calculus needs it.
#
#    It is tempting to require the attribute outright, and docs/modularity.md
#    did. It is not a core requirement: compiling with a plain binary `and`
#    leaves `__eo_invoke_assume_list`, the refutation test and the SMT
#    translation byte-identical. What changes is that the parser stops
#    accepting n-ary `(and a b c)`, which is surface syntax.
#
#    Where it does bite is `:list` premises. A rule that gathers its premises
#    with `and` builds the list through `__eo_nil`, and the `and` arm of
#    `__eo_nil` exists only because of the attribute; without it every such
#    rule goes Stuck. CPC has eleven such call sites, another calculus may have
#    none, so the requirement is conditional -- and both halves of it are
#    visible in what was just emitted.
if [ -f "${CORE_MODULE}" ]; then
  uses_and_premise_lists=0
  grep -q "__eo_mk_premise_list (Term.UOp UserOp.and)" "${CORE_MODULE}" && uses_and_premise_lists=1
  has_and_nil=0
  grep -qE "UserOp\.and\), *T => *\(?Term\.Boolean true" "${CORE_MODULE}" && has_and_nil=1
  if [ "${uses_and_premise_lists}" = "1" ] && [ "${has_and_nil}" = "0" ]; then
    contract_errors+=("rules gather \`:list\` premises with \`and\`, but \`and\` is not declared \`:right-assoc-nil true\`, so those rules cannot build a premise list")
  fi
fi

if [ "${#contract_errors[@]}" -gt 0 ]; then
  echo >&2
  echo "error: the signature does not meet the contract the checker relies on:" >&2
  printf '  - %s\n' "${contract_errors[@]}" >&2
  echo >&2
  echo "Declare the operator in the signature and give it its SMT-LIB meaning" >&2
  echo "in the semantics configuration. A calculus whose rules gather premises" >&2
  echo "with it also needs the nil attribute:" >&2
  echo >&2
  echo "  (declare-const and (-> Bool Bool Bool) :right-assoc-nil true)" >&2
  echo >&2
  echo "Nothing has been installed. See docs/modularity.md." >&2
  exit 1
fi
if [ "${uses_and_premise_lists:-0}" = "1" ]; then
  echo "    ok: \`and\`, translated to SmtTerm.and, with the nil its premise lists need"
else
  echo "    ok: \`and\`, translated to SmtTerm.and"
fi

if [ "${CHECK}" = "1" ]; then
  echo "==> Staging a copy of ${PACKAGE} to compare against"
else
  echo "==> Installing generated Lean files into ${DEST_DIR}"
fi
mkdir -p "${DEST_DIR}" "${DEST_DIR}/Proofs" "${DEST_DIR}/Proofs/Rules"
for name in "${LEAN_OUTPUTS[@]}"; do
  if [ "${NO_PARSER}" = "1" ] && [ "${name}" = "Parser.lean" ]; then
    rm -f "${DEST_DIR}/${name}"
    continue
  fi
  if [ ! -f "${LEAN_DIR}/${name}" ]; then
    echo "error: ${LEAN_DIR}/${name} was not generated." >&2
    exit 1
  fi
  [ "${CHECK}" = "1" ] || echo "    ${PACKAGE}/${name}"
  cp "${LEAN_DIR}/${name}" "${DEST_DIR}/${name}"
  prepend_header "${DEST_DIR}/${name}"
done

copied=0
preserved=0
if [ -d "${LEAN_DIR}/Proofs/Rules" ]; then
  shopt -s nullglob
  for file in "${LEAN_DIR}"/Proofs/Rules/*.lean; do
    rule_dest="${DEST_DIR}/Proofs/Rules/$(basename "${file}")"
    if [ -e "${rule_dest}" ]; then
      preserved=$((preserved + 1))
      continue
    fi
    cp "${file}" "${rule_dest}"
    copied=$((copied + 1))
  done
  shopt -u nullglob
  [ "${CHECK}" = "1" ] || \
    echo "    ${PACKAGE}/Proofs/Rules/*.lean (${copied} written, ${preserved} existing preserved)"
fi

# The generated files import each other under the name the compiler gave the
# calculus, which is the name of the signature file. Point them at the package
# they were just installed into, which for CpcMini is not that name.
SRC_CALC="$(detect_generated_calc "${LEAN_DIR}" || calc_name_of "${SIGNATURE}")"
if [ "${SRC_CALC}" != "${PACKAGE}" ]; then
  echo "==> Rewriting imports from ${SRC_CALC} to ${PACKAGE}"
  while IFS= read -r -d '' file; do
    sed_in_place \
      "s/import \\(all \\)\\{0,1\\}${SRC_CALC}\\./import \\1${PACKAGE}\\./g" \
      "${file}"
  done < <(find "${DEST_DIR}" -type f -name '*.lean' -print0)
fi

if [ "${NO_PARTIAL}" = "1" ]; then
  echo "==> Rewriting partial def to def in ${PACKAGE}"
  while IFS= read -r -d '' file; do
    sed_in_place 's/partial def /def /g' "${file}"
  done < <(find "${DEST_DIR}" -type f -name '*.lean' -print0)
fi

if [ "${CHECK}" = "1" ]; then
  staged="${CHECK_DIR}/staged.txt"
  current="${CHECK_DIR}/current.txt"
  ( cd "${DEST_DIR}" && find . -type f | sed 's|^\./||' | LC_ALL=C sort ) > "${staged}"
  if [ -d "${PACKAGE_DIR}" ]; then
    ( cd "${PACKAGE_DIR}" && find . -type f | sed 's|^\./||' | LC_ALL=C sort ) > "${current}"
  else
    : > "${current}"
  fi

  updates=0
  declare -a differing=()
  # The blank line belongs to the list, so it is printed with the first entry
  # rather than ahead of a list that may turn out to be empty.
  open_list() { if [ "${updates}" -eq 0 ]; then echo; fi; }
  while IFS= read -r rel; do
    if [ ! -e "${PACKAGE_DIR}/${rel}" ]; then
      open_list
      echo "  add     ${PACKAGE}/${rel}"
      updates=$((updates + 1))
    elif ! cmp -s "${DEST_DIR}/${rel}" "${PACKAGE_DIR}/${rel}"; then
      open_list
      echo "  update  ${PACKAGE}/${rel}"
      differing+=("${rel}")
      updates=$((updates + 1))
    fi
  done < "${staged}"
  while IFS= read -r rel; do
    if [ ! -e "${DEST_DIR}/${rel}" ]; then
      open_list
      echo "  remove  ${PACKAGE}/${rel}"
      updates=$((updates + 1))
    fi
  done < "${current}"

  if [ "${updates}" -eq 0 ]; then
    if [ "${BRIEF}" = "0" ]; then
      echo "==> ${PACKAGE} is up to date with ${SIGNATURE}."
      echo "Nothing was written."
    fi
    exit 0
  fi
  echo
  echo "==> ${PACKAGE} is NOT up to date with ${SIGNATURE}: ${updates} file(s)."

  # What differs, and not only that something does. The file names alone do not
  # say whether the calculus moved, whether someone edited generated code by
  # hand, or whether the same compiler emitted the same calculus differently --
  # and the last of those is exactly what a check running somewhere other than
  # the machine that generated the package is in a position to discover.
  if [ "${#differing[@]}" -gt 0 ]; then
    shown=0
    for rel in "${differing[@]}"; do
      [ "${shown}" -lt "${DIFF_FILES}" ] || break
      shown=$((shown + 1))
      echo
      { diff -u \
          --label "${PACKAGE}/${rel} as committed" \
          --label "${PACKAGE}/${rel} as compiled just now" \
          "${PACKAGE_DIR}/${rel}" "${DEST_DIR}/${rel}" || true; } |
        sed -n "1,${DIFF_LINES}p" | sed 's/^/  /'
    done
    if [ "${#differing[@]}" -gt "${DIFF_FILES}" ]; then
      echo
      echo "  ... and $(( ${#differing[@]} - DIFF_FILES )) more differing file(s)."
    fi
    echo
    echo "(each diff cut off at ${DIFF_LINES} lines; run the check yourself for all of it)"
  fi

  if [ "${BRIEF}" = "0" ]; then
    echo
    echo "Nothing was written. Rerun without --check to apply."
  fi
  exit 1
fi

# CI compiles the cached copy, not whatever signature happens to be on the
# machine that ran the install, so the copy has to stay the signature the
# packages were generated from. A full install of Cpc or CpcMini is the thing
# that makes it so, and records it here rather than leaving that to be
# remembered as a second command.
#
# The two runs that must not: --rules installed a reduced calculus rather than
# the signature, and another package says nothing about these two. Recording
# either would repoint what CI compiles at a signature nothing here was built
# from. They report instead. --cached compiled the copy itself, so there is
# nothing to record either way.
cache_action=""
if [ "${CACHED}" = "0" ]; then
  fresh_cache="$(mktemp "${TMPDIR:-/tmp}/install-cpc-cache.XXXXXX")"
  if flatten_signature "${SIGNATURE}" "${fresh_cache}" &&
     ! cmp -s "${fresh_cache}" "${CACHE_FILE}"; then
    if [ "${RULES_ASKED_FOR}" = "1" ]; then
      cache_action="skipped:--rules compiled a reduced calculus"
    elif [ "${PACKAGE}" != "Cpc" ] && [ "${PACKAGE}" != "CpcMini" ]; then
      cache_action="skipped:${PACKAGE} is not a package the copy speaks for"
    else
      mkdir -p "$(dirname "${CACHE_FILE}")"
      cp "${fresh_cache}" "${CACHE_FILE}"
      cache_action="updated"
    fi
  fi
  rm -f "${fresh_cache}"
fi

if [ "${BRIEF}" = "0" ]; then
  cat <<DONE

==> Done. ${PACKAGE} regenerated from ${SIGNATURE}.

${copied} rule file(s) written, ${preserved} preserved. Build with:

  scripts/build.sh ${PACKAGE}

A preserved rule file whose statement the calculus has changed will fail to
build; a newly written one has \`sorry\` for a proof. Review with git diff
before committing.
DONE
fi

# The copy is one thing however many packages are installed from it, so this
# says its piece once and in one line under --brief, where the caller has a
# closing summary of its own to give.
case "${cache_action}" in
  updated)
    if [ "${BRIEF}" = "1" ]; then
      echo "==> ${CACHE_FILE#"${repo_root}/"} now records this signature."
    else
      cat <<NOTE

==> ${CACHE_FILE#"${repo_root}/"} now records this signature.

That copy is what CI compiles, so commit it along with ${PACKAGE}.
NOTE
      version="$(signature_version "${SIGNATURE}")"
      [ -z "${version}" ] || cat <<NOTE

It was read at commit
  ${version}
which the copy does not record: put that in the commit message.
NOTE
      echo
    fi
    ;;
  skipped:*)
    if [ "${BRIEF}" = "1" ]; then
      echo "==> Note: ${CACHE_FILE#"${repo_root}/"} still records another signature," \
           "since ${cache_action#skipped:}."
    else
      cat <<NOTE

==> Note: the cached signature is not the one just compiled.

${CACHE_FILE#"${repo_root}/"} was left as it was, since ${cache_action#skipped:}.
It is what CI compiles, and a full install of Cpc or CpcMini is what records a
signature there:

  install/install-cpc.sh ${SIGNATURE}

NOTE
    fi
    ;;
esac
