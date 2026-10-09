#!/usr/bin/env python3
"""Executive summary of lines of code and proof in Cpc/.

Reports, by transitive Lean `import` closure (restricted to the `Cpc` and
`Logos` libraries):

  (1) Lines to *define* smt_satisfiability: SmtModel.lean and its dependencies.
      Compare directly with entry (1) of smt-std-loc-summary.py.
  (2) Additional lines to *define* eo_satisfiability: Spec.lean and its
      dependencies, excluding the SMT semantics of (1), followed by the total
      lines including (1).
  (3) Lines for the proof *checker*: Logos.lean and its dependencies.
  (4) Lines for the proof *parser*: Cpc/Parser.lean and its dependencies, minus
      the checker definitions of (3). This splits into the signature-independent
      parser of the `Logos` library and the generated `Cpc` configuration.
  (5) Lines for the central proof of correctness of the checker, partitioned
      into disjoint buckets (no file double-counted):
        (a) smt-model-eval type preservation
        (b) canonicity theorem
        (c) translation type preservation
        (d) non-vacuity
        (e) closedness/evaluation invariance
        (f) proofs of proof rule correctness
        (g) top-level checker correctness (the driver tying it together)

These pieces form a (nearly) linear dependency chain:

    definitions -> (a) -> (b) -> (c) -> (e) -> (f) -> (g)

with (d) non-vacuity a standalone leaf off (a). Canonicity (b) sits directly on
the smt-model layer (a); closedness/evaluation invariance (e) is the general
model-stability result used by checker/rule support; the rule proofs (f)
include the CheckerCore checker scaffolding they are stated against, and the
top-level theorem (g) imports the rules, so (g) depends on (f) and nothing
depends back on (g).

Attribution for (5) is priority-based: the definitions from (1)-(4) are
excluded first, then each file is owned by the earliest bucket whose import
closure reaches it. So the shared type-preservation foundation is counted once
under (a), and the rest report only their *incremental* lines. The buckets are
disjoint and sum to the whole proof.

A "line of code" is a non-blank, non-comment line (Lean line comments `--` and
nested block comments `/- ... -/` are stripped).

Usage:
  scripts/cpc-loc-summary.py            # summary (totals + per-bucket)
  scripts/cpc-loc-summary.py --files    # also list every file with its LOC
  scripts/cpc-loc-summary.py --deps     # also print the inter-piece dependencies
"""

from __future__ import annotations

import os
import re
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(SCRIPT_DIR)

# --- Bucket configuration -------------------------------------------------
# Each entry is (key, title, closure_roots, file_roots). A bucket owns the
# import closure of its `closure_roots` plus the literal modules in
# `file_roots`, minus anything an earlier bucket already claimed. Buckets are
# listed here in PRIORITY (attribution) order; the report shows them in
# DISPLAY_ORDER below.
#
# (g) is claimed before the (f) catch-all and uses `file_roots` (literal, not
# closure): Checker.lean / RuleLemmas.lean import every rule, so their closures
# would absorb all of (f). Attributing just those two files to (g) reserves the
# top-level theorem, and everything the rules build on -- including the
# CheckerCore scaffolding -- falls through to the (f) catch-all. The result is a
# linear chain ... -> (f) -> (g): (g) depends on (f), nothing depends on (g).
PROOF_BUCKETS = [
    ("a", "smt-model-eval type preservation", ["Cpc.Proofs.TypePreservation"], []),
    ("b", "canonicity theorem",               ["Cpc.Proofs.Canonical"], []),
    ("c", "translation type preservation",    ["Cpc.Proofs.Translation"], []),
    ("d", "non-vacuity",                       ["Cpc.Proofs.TypePreservation.Nonvacuity"], []),
    ("e", "closedness/evaluation invariance",  ["Cpc.Proofs.Closed.Support"], []),
    ("g", "top-level checker correctness",     [],
                                               ["Cpc.Proofs.Checker", "Cpc.Proofs.RuleLemmas",
                                                "Cpc.Api", "Cpc.ApiChecks", "Cpc.ApiCorrect"]),
    ("f", "proofs of proof rule correctness",  ["Cpc.Proofs.Checker"], []),  # catch-all
]

# Order pieces appear in the report (their natural dependency order).
DISPLAY_ORDER = ["a", "b", "c", "d", "e", "f", "g"]

# The full central proof (everything reachable from the top-level theorem).
CENTRAL_ROOTS = ["Cpc.Proofs.Checker"]

# Definitions to exclude from the proof partition (reported as (1)-(3)).
SMT_ROOTS = ["Cpc.SmtModel"]
SPEC_ROOTS = ["Cpc.Spec"]
LOGOS_ROOTS = ["Cpc.Logos"]

# The parser: the generated configuration plus the generic parser it plugs into.
PARSER_ROOTS = ["Cpc.Parser"]

# The libraries whose modules are counted.
LIBRARIES = ["Cpc", "Logos"]


# --- Import graph ---------------------------------------------------------
# Lean's module system spells imports `public import M`, `import all M`, and
# `public import all M` in addition to plain `import M`.
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(?:all\s+)?((?:Cpc|Logos)[\w.]*)")


def module_to_path(module: str) -> str:
    return os.path.join(REPO_ROOT, module.replace(".", "/") + ".lean")


def path_to_module(path: str) -> str:
    rel = os.path.relpath(path, REPO_ROOT)
    return rel[:-len(".lean")].replace("/", ".")


def build_graph() -> tuple[dict[str, set[str]], set[str]]:
    imports: dict[str, set[str]] = {}
    modules: set[str] = set()
    for library in LIBRARIES:
        for dirpath, _, files in os.walk(os.path.join(REPO_ROOT, library)):
            for name in files:
                if not name.endswith(".lean"):
                    continue
                path = os.path.join(dirpath, name)
                module = path_to_module(path)
                modules.add(module)
                deps: set[str] = set()
                with open(path, encoding="utf-8") as fh:
                    for line in fh:
                        m = IMPORT_RE.match(line)
                        if m:
                            deps.add(m.group(1))
                imports[module] = deps
    return imports, modules


def closure(roots, imports, modules) -> set[str]:
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module in seen or module not in modules:
            continue
        seen.add(module)
        stack.extend(imports.get(module, ()))
    return seen


# --- LOC counting (non-blank, non-comment, Lean-aware) --------------------
def count_loc(path: str) -> int:
    """Count non-blank, non-comment lines, stripping Lean comments.

    Handles `--` line comments and nested `/- ... -/` block comments
    (docstrings `/-- -/` are block comments too). Does not special-case `--`
    inside string literals, which is rare in proof code.
    """
    with open(path, encoding="utf-8") as fh:
        text = fh.read()

    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0  # block-comment nesting depth
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
        # not in a block comment
        if text.startswith("--", i):
            # skip to end of line (line comment)
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1

    count = 0
    for line in "".join(out).splitlines():
        if line.strip():
            count += 1
    return count


def loc_of(module: str, cache: dict[str, int]) -> int:
    if module in cache:
        return cache[module]
    path = module_to_path(module)
    value = count_loc(path) if os.path.exists(path) else 0
    cache[module] = value
    return value


def total_loc(modules, cache) -> int:
    return sum(loc_of(m, cache) for m in modules)


# --- Reporting ------------------------------------------------------------
def print_file_list(modules, cache, indent="    "):
    for module in sorted(modules, key=lambda m: (-loc_of(m, cache), m)):
        print(f"{indent}{loc_of(module, cache):6d}  {module}")


def print_dependencies(owner, imports, titles):
    """Print the direct cross-bucket import edges (X imports from Y)."""
    edges = {k: set() for k in DISPLAY_ORDER}
    for module, deps in imports.items():
        src = owner.get(module)
        if src not in edges:
            continue
        for dep in deps:
            dst = owner.get(dep)
            if dst is not None and dst != src:
                edges[src].add(dst)

    rank = {k: i for i, k in enumerate(["def"] + DISPLAY_ORDER)}
    print("\n(6) Dependencies between proof pieces (X imports from Y)")
    for key in DISPLAY_ORDER:
        deps = sorted(edges[key], key=lambda d: rank.get(d, 99))
        shown = ", ".join("definitions" if d == "def" else f"({d})" for d in deps)
        print(f"    ({key}) {titles[key]}")
        print(f"         depends on: {shown or '(none)'}")


def main() -> int:
    show_files = "--files" in sys.argv[1:]
    show_deps = "--deps" in sys.argv[1:]

    imports, modules = build_graph()
    cache: dict[str, int] = {}

    smt_cl = closure(SMT_ROOTS, imports, modules)
    spec_cl = closure(SPEC_ROOTS, imports, modules)
    eo_cl = spec_cl - smt_cl
    logos_cl = closure(LOGOS_ROOTS, imports, modules)
    parser_cl = closure(PARSER_ROOTS, imports, modules) - logos_cl
    central_cl = closure(CENTRAL_ROOTS, imports, modules)

    print("=" * 70)
    print("CPC executive summary  (LOC = non-blank, non-comment lines)")
    print("=" * 70)

    # (1) SMT semantics, measured like the SmtStd report's first entry.
    print("\n(1) Definition of smt_satisfiability  [Cpc.SmtModel + dependencies]")
    print(f"    files: {len(smt_cl):4d}    lines: {total_loc(smt_cl, cache):7d}")
    print_file_list(smt_cl, cache)

    # (2) Eunoia satisfiability on top of the SMT semantics, without recounting it.
    print("\n(2) Definition of eo_satisfiability  [Cpc.Spec + dependencies, excluding (1)]")
    print(f"    files: {len(eo_cl):4d}    lines: {total_loc(eo_cl, cache):7d}")
    print_file_list(eo_cl, cache)
    print(f"    total lines including SMT semantics [(1) + (2)]: {total_loc(smt_cl | eo_cl, cache):7d}")

    # (3) proof checker
    print("\n(3) Proof checker  [Cpc.Logos + dependencies]")
    print(f"    files: {len(logos_cl):4d}    lines: {total_loc(logos_cl, cache):7d}")
    print_file_list(logos_cl, cache)

    # (4) proof parser: the generic parser plus the generated configuration.
    # The checker definitions of (3) are excluded, since the configuration
    # imports them to build terms.
    generic = {m for m in parser_cl if m.startswith("Logos")}
    generated = parser_cl - generic
    print("\n(4) Proof parser  [Cpc.Parser + dependencies, excluding (3)]")
    print(f"    files: {len(parser_cl):4d}    lines: {total_loc(parser_cl, cache):7d}")
    print(f"        signature-independent parser: {total_loc(generic, cache):7d}")
    print(f"        generated configuration:      {total_loc(generated, cache):7d}")
    print_file_list(parser_cl, cache)

    # (5) central proof of correctness, partitioned.
    # The "proof universe" is everything reachable from the top-level theorem
    # PLUS the bucket roots. Non-vacuity (d) is a standalone meta-theorem that
    # nothing imports, so it is not in the central closure but is still part of
    # the correctness story the buckets account for.
    excluded = smt_cl | spec_cl | logos_cl | parser_cl
    print("\n(5) Central proof of correctness of the checker")
    print("    (definitions from (1)-(4) excluded; buckets disjoint, priority-attributed)")

    claimed = set(excluded)
    owner = {m: "def" for m in excluded}
    results = {}
    titles = {}
    for key, title, closure_roots, file_roots in PROOF_BUCKETS:
        bucket_cl = closure(closure_roots, imports, modules)
        bucket_cl |= {m for m in file_roots if m in modules}
        own = bucket_cl - claimed
        claimed |= own
        for module in own:
            owner[module] = key
        results[key] = own
        titles[key] = title

    proof_total = total_loc(claimed - excluded, cache)
    proof_files = len(claimed - excluded)
    print(f"    total proof files: {proof_files:4d}    total proof lines: {proof_total:7d}")

    for key in DISPLAY_ORDER:
        own = results[key]
        note = "  (standalone; not imported by the top-level theorem)" if key == "d" else ""
        print(f"\n    ({key}) {titles[key]}{note}")
        print(f"        files: {len(own):4d}    lines: {total_loc(own, cache):7d}")
        if show_files:
            print_file_list(own, cache, indent="        ")

    if show_deps:
        print_dependencies(owner, imports, titles)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
