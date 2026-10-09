#!/usr/bin/env python3
"""Lines-of-code summary for the Logos Standard SMT-LIB semantics definition.

Like cpc-loc-summary.py, count non-blank, non-comment Lean lines by transitive
import closure. Only SmtStd modules are counted, with each file counted once.
Report the semantics and the library entry point separately, then their total.

Uses the CPC script's counting convention: strip `--` line comments and nested
`/- ... -/` block comments, without special treatment of string literals.

Usage:
  scripts/smt-std-loc-summary.py            # summary
  scripts/smt-std-loc-summary.py --files    # also list every file with its LOC
  scripts/smt-std-loc-summary.py --deps     # also print module dependencies
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys


REPO_ROOT = Path(__file__).resolve().parent.parent
MODEL_ROOT = "SmtStd.SmtModel"
LIBRARY_ROOT = "SmtStd"
IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import\s+(?:all\s+)?(SmtStd(?:\.[\w]+)*)(?=\s|$)"
)


# --- LOC counting (same convention as cpc-loc-summary.py) ------------------
def count_loc(text: str) -> int:
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    return sum(1 for line in "".join(out).splitlines() if line.strip())


# --- Import graph ---------------------------------------------------------
def read_modules(roots: list[str]) -> tuple[dict[str, set[str]], dict[str, int]]:
    imports: dict[str, set[str]] = {}
    loc: dict[str, int] = {}
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module in imports:
            continue
        path = REPO_ROOT / (module.replace(".", "/") + ".lean")
        text = path.read_text(encoding="utf-8")
        deps = set()
        for line in text.splitlines():
            match = IMPORT_RE.match(line)
            if match:
                deps.add(match.group(1))
        imports[module] = deps
        loc[module] = count_loc(text)
        stack.extend(deps)
    return imports, loc


def closure(root: str, imports: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    stack = [root]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        stack.extend(imports[module])
    return seen


# --- Reporting ------------------------------------------------------------
def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--files", action="store_true", help="list each file and its LOC")
    parser.add_argument("--deps", action="store_true", help="show direct module imports")
    args = parser.parse_args()

    try:
        imports, loc = read_modules([MODEL_ROOT, LIBRARY_ROOT])
    except OSError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    model = closure(MODEL_ROOT, imports)
    library = closure(LIBRARY_ROOT, imports) | model
    entry = library - model

    print("=" * 70)
    print("Logos Standard SMT-LIB semantics definition")
    print("Executive summary  (LOC = non-blank, non-comment lines)")
    print("=" * 70)

    for title, modules in (
        ("(1) Definition of smt_satisfiability  [SmtStd.SmtModel + dependencies]", model),
        ("(2) Library entry point  [SmtStd + dependencies, excluding (1)]", entry),
    ):
        print(f"\n{title}")
        print(f"    files: {len(modules):4d}    lines: {sum(loc[m] for m in modules):7d}")
        if args.files:
            for module in sorted(modules, key=lambda m: (-loc[m], m)):
                print(f"    {loc[module]:6d}  {module}")

    print("\nTotal library  [each file counted once; external libraries excluded]")
    print(f"    files: {len(library):4d}    lines: {sum(loc[m] for m in library):7d}")

    if args.deps:
        print("\n(3) Dependencies between modules (X imports from Y)")
        for module in sorted(library):
            print(f"    {module}")
            print(f"         depends on: {', '.join(sorted(imports[module])) or '(none)'}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
