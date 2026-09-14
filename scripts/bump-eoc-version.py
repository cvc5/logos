#!/usr/bin/env python3
"""Internal-use-only helper for advancing Logos to the development EOC.

The development compiler is temporarily taken from cvc5/ethos's ``ethosEoc3``
branch. Advance the pinned commit to that branch's current head, synchronize
Logos's CPC semantics with the development copy from the same commit, build the
compiler, and regenerate CPC from the cached signature.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
PIN_FILE = REPO_ROOT / "install" / "get-eo-compiler.sh"
CPC_FILE = REPO_ROOT / "install" / "defs" / "Cpc.eos"
GET_EO_COMPILER = REPO_ROOT / "install" / "get-eo-compiler.sh"
INSTALL_CPC = REPO_ROOT / "install" / "install-cpc.sh"

ETHOS_REMOTE = "https://github.com/cvc5/ethos.git"
ETHOS_RAW = "https://raw.githubusercontent.com/cvc5/ethos"
ETHOS_BRANCH = "ethosEoc3"
ETHOS_CPC = "tools/eoc/semantics/development-cpc.eos"

COMMIT_RE = re.compile(r"[0-9a-f]{40}")
PIN_RE = re.compile(r'(?m)^ETHOS_VERSION="([0-9a-f]{40})"$')
PIN_COMMENT_RE = re.compile(
    r"(?m)^# [0-9a-f]{8} is the head of ethosEoc3, the temporary development branch\.$"
)

# The upstream file describes itself as an Ethos test fixture.  Once copied
# here, it is the authoritative Logos configuration, so keep that one paragraph
# accurate while copying the rest from Ethos verbatim.
UPSTREAM_OWNERSHIP = """\
; This one is of CPC and is kept as a test, so that the compiler and every stage
; after it have a real signature to run over. The official semantics of CPC
; lives in the Logos repository, which is what a run that means to say something
; about CPC names with --semantics; nothing keeps this copy in step with it.
"""
LOGOS_OWNERSHIP = """\
; This is the semantics of CPC and this file is where it lives. The development
; copy under tools/eoc/semantics in the ethos tree is also a compiler fixture;
; scripts/bump-eoc-version.py synchronizes this file from that copy when the
; pinned development compiler is advanced.
"""


class BumpError(RuntimeError):
    """An expected part of the development bump could not be completed."""


def latest_commit() -> str:
    """Return the commit currently at the development branch's remote ref."""
    command = [
        "git",
        "ls-remote",
        "--exit-code",
        ETHOS_REMOTE,
        f"refs/heads/{ETHOS_BRANCH}",
    ]
    try:
        result = subprocess.run(
            command,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except FileNotFoundError as error:
        raise BumpError("git is required but was not found on PATH") from error
    except subprocess.CalledProcessError as error:
        detail = error.stderr.strip() or "git ls-remote failed"
        raise BumpError(f"could not read {ETHOS_BRANCH} from Ethos: {detail}") from error

    fields = result.stdout.split()
    if len(fields) != 2 or not COMMIT_RE.fullmatch(fields[0]):
        raise BumpError(f"unexpected git ls-remote output: {result.stdout.strip()!r}")
    return fields[0]


def development_cpc(commit: str) -> str:
    """Download and lightly validate development-cpc.eos at ``commit``."""
    url = f"{ETHOS_RAW}/{commit}/{ETHOS_CPC}"
    request = urllib.request.Request(url, headers={"User-Agent": "logos-eoc-bump"})
    try:
        with urllib.request.urlopen(request) as response:
            source = response.read().decode("utf-8")
    except (OSError, UnicodeError, urllib.error.URLError) as error:
        raise BumpError(f"could not download {url}: {error}") from error

    if "(section \"The core symbols\")" not in source or "$eo_to_smt" not in source:
        raise BumpError(f"downloaded {ETHOS_CPC} does not look like CPC semantics")
    if source.count(UPSTREAM_OWNERSHIP) != 1:
        raise BumpError(
            f"the ownership notice in {ETHOS_CPC} changed; update this internal helper"
        )
    return source.replace(UPSTREAM_OWNERSHIP, LOGOS_OWNERSHIP, 1)


def updated_pin(source: str, commit: str) -> str:
    """Replace both the machine-readable pin and its nearby short hash."""
    if len(PIN_RE.findall(source)) != 1:
        raise BumpError(f"expected exactly one ETHOS_VERSION pin in {PIN_FILE}")
    source = PIN_RE.sub(f'ETHOS_VERSION="{commit}"', source)

    if len(PIN_COMMENT_RE.findall(source)) != 1:
        raise BumpError(f"expected exactly one ethosEoc3 pin comment in {PIN_FILE}")
    return PIN_COMMENT_RE.sub(
        f"# {commit[:8]} is the head of ethosEoc3, the temporary development branch.",
        source,
    )


def replace_file(path: Path, source: str) -> bool:
    """Atomically replace ``path`` if its UTF-8 contents changed."""
    if path.read_text(encoding="utf-8") == source:
        return False

    mode = path.stat().st_mode
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
            "w", encoding="utf-8", dir=path.parent, delete=False
        ) as output:
            temporary = Path(output.name)
            output.write(source)
        os.chmod(temporary, mode)
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return True


def run_step(description: str, command: list[str]) -> None:
    """Run one setup step with its output connected to this process."""
    print(f"\n==> {description}", flush=True)
    try:
        subprocess.run(command, cwd=REPO_ROOT, check=True)
    except FileNotFoundError as error:
        raise BumpError(f"could not run {command[0]}: file not found") from error
    except subprocess.CalledProcessError as error:
        raise BumpError(
            f"{description} failed with exit status {error.returncode}"
        ) from error


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Internal use only: pin EOC to the head of ethosEoc3 and copy its "
            "development CPC semantics into Logos, build the compiler, and "
            "regenerate CPC from the cached signature."
        )
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    parse_args(argv)
    try:
        commit = latest_commit()
        cpc_source = development_cpc(commit)
        pin_source = updated_pin(PIN_FILE.read_text(encoding="utf-8"), commit)
        pin_changed = replace_file(PIN_FILE, pin_source)
        cpc_changed = replace_file(CPC_FILE, cpc_source)
        print(f"ethosEoc3: {commit}")
        print(
            f"{'updated' if pin_changed else 'unchanged'}: "
            f"{PIN_FILE.relative_to(REPO_ROOT)}"
        )
        print(
            f"{'updated' if cpc_changed else 'unchanged'}: "
            f"{CPC_FILE.relative_to(REPO_ROOT)}"
        )
        run_step("Building the pinned EOC compiler", [str(GET_EO_COMPILER)])
        run_step(
            "Regenerating CPC from the cached signature",
            [str(INSTALL_CPC), "--all", "--cached"],
        )
    except (BumpError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
