#!/usr/bin/env bash

# Configure Lake to use host build tools when the tools bundled with Lean cannot
# start on this machine. This is most commonly needed on older Linux systems,
# where Lean itself runs but its bundled LLVM/Clang requires newer glibc symbols:
# a direct `lake build` there fails with errors such as `GLIBC_2.27 not found` or
# `GLIBC_2.29 not found` from the toolchain's bin/clang.
#
# The fallback selects the host C compiler and archiver through LEAN_CC and
# LEAN_AR while preserving the link-library paths of the Lean toolchain, so it
# needs a working host toolchain: GCC or Clang plus `ar`.
#
# Where that is unavailable, use a newer container or build the pinned Lean
# toolchain locally; do not replace the system libm.so.6 or glibc in place.
# Official x86-64 Lean binaries require glibc 2.26 or newer, which
# `getconf GNU_LIBC_VERSION` reports.
#
# This file is intended to be sourced by other scripts.

logos_configure_lean_toolchain() {
  if ! command -v lean >/dev/null 2>&1; then
    echo "Lean is not installed or is not on PATH. Install elan, then retry." >&2
    return 1
  fi

  local lean_sysroot
  if ! lean_sysroot="$(lean --print-prefix)"; then
    echo "Could not determine the active Lean toolchain directory." >&2
    return 1
  fi

  local bundled_cc="${lean_sysroot}/bin/clang"
  local bundled_ar="${lean_sysroot}/bin/llvm-ar"
  local bundled_cc_error=""
  local bundled_ar_error=""
  local use_host_cc=false
  local use_host_ar=false

  if [ -z "${LEAN_CC:-}" ] && [ -x "${bundled_cc}" ]; then
    if ! bundled_cc_error="$("${bundled_cc}" --version 2>&1)"; then
      use_host_cc=true
    fi
  fi

  if [ -z "${LEAN_AR:-}" ] && [ -x "${bundled_ar}" ]; then
    if ! bundled_ar_error="$("${bundled_ar}" --version 2>&1)"; then
      use_host_ar=true
    fi
  fi

  if [ "${use_host_cc}" = true ]; then
    local host_cc="${CC:-cc}"
    if ! command -v "${host_cc}" >/dev/null 2>&1; then
      echo "Lean's bundled C compiler cannot run:" >&2
      printf '%s\n' "${bundled_cc_error}" >&2
      echo "No host C compiler named '${host_cc}' was found." >&2
      echo "Install GCC or Clang, or set LEAN_CC to a compatible compiler." >&2
      return 1
    fi
    export LEAN_CC="${host_cc}"

    # Lake omits the bundled compiler's private sysroot flags when LEAN_CC is
    # set. Keep the host compiler, but make Lean's bundled third-party
    # libraries (GMP, libuv, and libc++) available to its linker. This avoids
    # requiring development packages that happen to match the Lean release.
    local lean_library_path="${lean_sysroot}/lib:${lean_sysroot}/lib/libc"
    if [ -n "${LIBRARY_PATH:-}" ]; then
      lean_library_path="${lean_library_path}:${LIBRARY_PATH}"
    fi
    export LIBRARY_PATH="${lean_library_path}"

    echo "Lean's bundled C compiler cannot run; using host compiler '${LEAN_CC}'." >&2
    if [ -n "${bundled_cc_error}" ]; then
      printf '%s\n' "${bundled_cc_error}" >&2
    fi
  fi

  if [ "${use_host_ar}" = true ] || { [ "${use_host_cc}" = true ] && [ -z "${LEAN_AR:-}" ]; }; then
    local host_ar="${AR:-ar}"
    if ! command -v "${host_ar}" >/dev/null 2>&1; then
      if [ -n "${bundled_ar_error}" ]; then
        echo "Lean's bundled archiver cannot run:" >&2
        printf '%s\n' "${bundled_ar_error}" >&2
      fi
      echo "No host archiver named '${host_ar}' was found." >&2
      echo "Install binutils, or set LEAN_AR to a compatible archiver." >&2
      return 1
    fi
    export LEAN_AR="${host_ar}"
    echo "Using host archiver '${LEAN_AR}'." >&2
  fi
}
