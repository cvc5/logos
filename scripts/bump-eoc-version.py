#!/usr/bin/env python3
"""Internal-use-only helper for advancing Logos to the latest EOC on Ethos main.

Advance the pinned commit to the current head of cvc5/ethos's ``main``, build the
compiler, and regenerate Cpc and CpcMini from the cached signature. The CPC
semantics in install/defs/Cpc.eos is maintained in Logos and is not touched.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
PIN_FILE = REPO_ROOT / "install" / "get-eo-compiler.sh"
GET_EO_COMPILER = REPO_ROOT / "install" / "get-eo-compiler.sh"
INSTALL_CPC = REPO_ROOT / "install" / "install-cpc.sh"

ETHOS_REMOTE = "https://github.com/cvc5/ethos.git"
ETHOS_BRANCH = "main"

COMMIT_RE = re.compile(r"[0-9a-f]{40}")
PIN_RE = re.compile(r'(?m)^ETHOS_VERSION="([0-9a-f]{40})"$')


class BumpError(RuntimeError):
    """An expected part of the compiler bump could not be completed."""


def latest_commit() -> str:
    """Return the commit currently at Ethos main's remote ref."""
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


def updated_pin(source: str, commit: str) -> str:
    """Replace the machine-readable compiler pin."""
    if len(PIN_RE.findall(source)) != 1:
        raise BumpError(f"expected exactly one ETHOS_VERSION pin in {PIN_FILE}")
    return PIN_RE.sub(f'ETHOS_VERSION="{commit}"', source)


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
            "Internal use only: pin EOC to the latest commit on Ethos main, build the "
            "compiler, and regenerate Cpc and CpcMini from the cached signature."
        )
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    parse_args(argv)
    try:
        commit = latest_commit()
        pin_source = updated_pin(PIN_FILE.read_text(encoding="utf-8"), commit)
        pin_changed = replace_file(PIN_FILE, pin_source)
        print(f"Ethos {ETHOS_BRANCH}: {commit}")
        print(
            f"{'updated' if pin_changed else 'unchanged'}: "
            f"{PIN_FILE.relative_to(REPO_ROOT)}"
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
