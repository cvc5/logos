#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: install/get-eo-compiler.sh [OPTION]...

Download and build the Eunoia compiler that install/install-cpc.sh runs: the
ethos source tree, pinned to the commit recorded in ETHOS_VERSION below, and
ethos-eoc built from the standalone project in its plugins/ directory.

Both are placed under install/deps/ (see --deps-dir) and the resulting paths
and version are recorded in install/deps/eoc-env.sh, which install-cpc.sh reads
so that the signature is the only thing it has to be told.

This sets up the compiler and nothing else. The Eunoia signature to compile is
not fetched here and is not a concern of this script; name one when running
install/install-cpc.sh.

ethos-eoc is always compiled here rather than downloaded. No release of ethos
publishes it, and it reads its Lean and Eunoia templates out of the source tree
it was built from, so that tree has to be fetched either way.

The ethos commit is not an option. It is pinned in this script, so that what
the compiler emits changes only when someone moves the pin deliberately. Move
it and perform the complete update with the internal
scripts/bump-eoc-version.py helper.

Options:
  --deps-dir DIR       where to put everything (default: <install>/deps)
  --jobs N             parallel compile jobs (default: all processors)
  --keep-tmp           keep the downloaded archive instead of deleting it
  -h, --help           show this message

Requires cmake >= 3.12, a C++17 compiler, the GMP development headers, tar, and
either wget or curl. On Debian and Ubuntu the GMP headers are libgmp-dev; on
macOS with Homebrew they are gmp.

Examples:
  install/get-eo-compiler.sh
  install/get-eo-compiler.sh --jobs 8
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

# The pinned commit of cvc5/ethos used to build the Eunoia compiler.
# 1821e283 is the head of ethosEoc3, the temporary development branch.
#
# TODO: this is a workaround. ethosEoc3 is a development branch, and the pin
# belongs on a commit of ethos main; move it back once what this needs is
# there. It is pinned to a commit of the branch rather than to the branch
# itself, so that what the compiler emits still changes only on purpose.
ETHOS_VERSION="ce7ce77e9f13125633aa41740783e1a8ef4f6fef"
DEPS_DIR=""
JOBS=""
KEEP_TMP=0

while [ $# -gt 0 ]; do
  case "$1" in
    --deps-dir) DEPS_DIR="${2:?--deps-dir requires a value}"; shift 2 ;;
    --deps-dir=*) DEPS_DIR="${1#*=}"; shift ;;
    --jobs) JOBS="${2:?--jobs requires a value}"; shift 2 ;;
    --jobs=*) JOBS="${1#*=}"; shift ;;
    --keep-tmp) KEEP_TMP=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unrecognized option $1" >&2; usage >&2; exit 2 ;;
  esac
done

DEPS_DIR="$(expand_tilde "${DEPS_DIR}")"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DEPS_DIR="${DEPS_DIR:-${script_dir}/deps}"

if [ -z "${JOBS}" ]; then
  if command -v nproc >/dev/null 2>&1; then
    JOBS="$(nproc)"
  elif command -v sysctl >/dev/null 2>&1; then
    JOBS="$(sysctl -n hw.logicalcpu 2>/dev/null || echo 4)"
  else
    JOBS=4
  fi
fi

# Download $1 to $2.
download() {
  if command -v wget >/dev/null 2>&1; then
    wget -c -O "$2" "$1"
  elif command -v curl >/dev/null 2>&1; then
    curl -Lf "$1" -o "$2"
  else
    echo "Neither wget nor curl is installed; cannot download $1." >&2
    exit 1
  fi
}

for tool in cmake tar; do
  command -v "${tool}" >/dev/null 2>&1 || {
    echo "${tool} is required but was not found on PATH." >&2
    exit 1
  }
done

TMP_DIR="${DEPS_DIR}/tmp"
ETHOS_DIR="${DEPS_DIR}/ethos"
BUILD_DIR="${ETHOS_DIR}/build-eoc"
mkdir -p "${TMP_DIR}"

echo "==> Downloading ethos ${ETHOS_VERSION}"
download "https://github.com/cvc5/ethos/archive/${ETHOS_VERSION}.tar.gz" \
  "${TMP_DIR}/ethos.tgz"
rm -rf "${ETHOS_DIR}"
mkdir -p "${ETHOS_DIR}"
# --strip-components drops the leading directory a GitHub archive wraps
# everything in.
tar --strip-components 1 -xzf "${TMP_DIR}/ethos.tgz" -C "${ETHOS_DIR}"

DRIVER="${ETHOS_DIR}/tools/eoc/driver.py"
if [ ! -f "${DRIVER}" ]; then
  echo "error: ${DRIVER} is missing from the ethos tree." >&2
  echo "ETHOS_VERSION in this script is pinned to ${ETHOS_VERSION}," >&2
  echo "which should contain it; a pin moved to an older commit may not." >&2
  exit 1
fi

echo "==> Building ethos-eoc with ${JOBS} jobs"
if ! cmake -S "${ETHOS_DIR}/plugins" -B "${BUILD_DIR}" -DCMAKE_BUILD_TYPE=Release; then
  echo >&2
  echo "error: configuring ethos-eoc failed. It needs cmake >= 3.12, a C++17" >&2
  echo "compiler and the GMP development headers (libgmp-dev on Debian and" >&2
  echo "Ubuntu, gmp on Homebrew)." >&2
  exit 1
fi
cmake --build "${BUILD_DIR}" --parallel "${JOBS}" --target ethos-eoc

ETHOS_EOC="${BUILD_DIR}/ethos-eoc"
if [ ! -x "${ETHOS_EOC}" ]; then
  echo "error: the build reported success but ${ETHOS_EOC} is not there." >&2
  exit 1
fi

# The binary is left where it was built on purpose. It resolves its templates
# against the source tree that configured it, so moving it apart from
# ${ETHOS_DIR} would only work with ETHOS_PLUGIN_ROOT set to point back.

echo "==> Recording what was installed in ${DEPS_DIR}/eoc-env.sh"
cat > "${DEPS_DIR}/eoc-env.sh" <<ENV
# Written by install/get-eo-compiler.sh. Read by install/install-cpc.sh so that
# it only has to be told which signature to compile. Edit by re-running
# get-eo-compiler.sh rather than by hand.
#
# ethos ${ETHOS_VERSION}
EOC_ETHOS_DIR="${ETHOS_DIR}"
EOC_ETHOS_EOC="${ETHOS_EOC}"
EOC_BUILD_DIR="${BUILD_DIR}"
EOC_ETHOS_VERSION="${ETHOS_VERSION}"
ENV

if [ "${KEEP_TMP}" = "0" ]; then
  rm -rf "${TMP_DIR}"
fi

cat <<DONE

==> Done.

  ethos      ${ETHOS_DIR} (${ETHOS_VERSION})
  ethos-eoc  ${ETHOS_EOC}

Compile a Eunoia signature with, e.g.

  install/install-cpc.sh <cvc5>/proofs/eo/cpc/Cpc.eo

which reads ${DEPS_DIR}/eoc-env.sh for everything else.
DONE
