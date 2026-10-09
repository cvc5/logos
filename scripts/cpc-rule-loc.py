#!/usr/bin/env python3
"""Per-proof-rule lines-of-code summary for Cpc/Proofs/Rules.

For every proof rule (each `Cpc/Proofs/Rules/<Rule>.lean`) it reports two
numbers, neither of which is a partition -- shared code is counted once per
rule that pulls it in:

  PROOF  Lines of the rule's correctness proof: the rule file plus every proof
         file it transitively imports, EXCLUDING dependencies that belong to
         the lower proof layers
            (a) smt-model-eval type preservation,
            (b) canonicity,
            (c) translation type preservation,
         and excluding the definitional base (Spec/Logos and their deps, i.e.
         what the proof is *about*). What remains is the rule file plus the
         shared rule-support / checker scaffolding it builds on. Because that
         shared support (e.g. files under RuleSupport/) is counted for every
         rule that imports it, the PROOF column does not sum to a partition.

  EO_PROG (bonus) Lines of the rule's corresponding `__eo_prog_<rule>`
         implementation in the checker (Cpc.Logos) plus every definition it
         transitively calls (helper functions and the datatypes they use).
         Shared helpers are again counted once per rule -- not a partition.

A "line of code" is non-blank and non-comment (Lean `--` line comments and
nested `/- ... -/` block comments are stripped).

Usage:
  scripts/cpc-rule-loc.py                # table sorted by PROOF loc (desc)
  scripts/cpc-rule-loc.py --sort=prog    # sort by EO_PROG loc
  scripts/cpc-rule-loc.py --sort=name    # sort alphabetically
  scripts/cpc-rule-loc.py --csv          # machine-readable CSV
"""

from __future__ import annotations

import os
import re
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(SCRIPT_DIR)
RULES_DIR = os.path.join(REPO_ROOT, "Cpc", "Proofs", "Rules")

# Proof layers excluded from the per-rule PROOF count (see module docstring).
EXCLUDE_ROOTS = [
    "Cpc.Spec",                       # SMT and eo_satisfiability definitions
    "Cpc.Logos",                      # proof checker definitions
    "Cpc.Proofs.TypePreservation",    # (a)
    "Cpc.Proofs.Canonical",           # (b)
    "Cpc.Proofs.Translation",         # (c)
]

# Files defining the checker's executable rule implementations (`__eo_prog_*`)
# and everything they can call.
CHECKER_FILES = ["Cpc/Logos.lean", "Cpc/LogosTerm.lean", "Cpc/SmtEval.lean"]


# --- Shared LOC counter (non-blank, non-comment, Lean-aware) --------------
def count_loc_text(text: str) -> int:
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


# --- File-level import graph (for the PROOF column) -----------------------
# Lean's module system spells imports `public import M`, `import all M`, and
# `public import all M` in addition to plain `import M`.
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(?:all\s+)?(Cpc[\w.]+)")


def module_path(module: str) -> str:
    return os.path.join(REPO_ROOT, module.replace(".", "/") + ".lean")


def build_import_graph():
    imports: dict[str, set[str]] = {}
    modules: set[str] = set()
    for dirpath, _, files in os.walk(os.path.join(REPO_ROOT, "Cpc")):
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            module = os.path.relpath(path, REPO_ROOT)[:-len(".lean")].replace("/", ".")
            modules.add(module)
            deps: set[str] = set()
            with open(path, encoding="utf-8") as fh:
                for line in fh:
                    m = IMPORT_RE.match(line)
                    if m:
                        deps.add(m.group(1))
            imports[module] = deps
    return imports, modules


def import_closure(roots, imports, modules) -> set[str]:
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module in seen or module not in modules:
            continue
        seen.add(module)
        stack.extend(imports.get(module, ()))
    return seen


# --- Definition-level call graph (for the EO_PROG column) -----------------
DECL_RE = re.compile(
    r"^(?:private |public |noncomputable |partial |protected |unsafe )*"
    r"(?:def|abbrev|theorem|lemma|inductive|structure|instance)\s+"
    r"(?:@\[[^\]]*\]\s*)?([A-Za-z_][A-Za-z0-9_'!?]*)"
)
# Lines that end the current declaration without starting a new named one.
BOUNDARY_RE = re.compile(
    r"^(?:public )?"
    r"(mutual|end|namespace|open|set_option|import|attribute|section|variable|module)\b"
    r"|^/-"
)
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")


def build_def_graph(files):
    """Return (loc_by_name, deps_by_name) for top-level decls in `files`.

    Names that are defined more than once (e.g. across `mutual` blocks) have
    their bodies concatenated.
    """
    bodies: dict[str, list[str]] = {}
    for rel in files:
        path = os.path.join(REPO_ROOT, rel)
        current = None
        buf: list[str] = []
        for line in open(path, encoding="utf-8").read().split("\n"):
            decl = DECL_RE.match(line)
            if decl:
                if current is not None:
                    bodies.setdefault(current, []).append("\n".join(buf))
                current = decl.group(1)
                buf = [line]
            elif BOUNDARY_RE.match(line):
                if current is not None:
                    bodies.setdefault(current, []).append("\n".join(buf))
                current = None
                buf = []
            elif current is not None:
                buf.append(line)
        if current is not None:
            bodies.setdefault(current, []).append("\n".join(buf))

    names = set(bodies)
    loc_by_name: dict[str, int] = {}
    deps_by_name: dict[str, set[str]] = {}
    for name, parts in bodies.items():
        text = "\n".join(parts)
        loc_by_name[name] = count_loc_text(text)
        refs = set(TOKEN_RE.findall(text)) & names
        refs.discard(name)
        deps_by_name[name] = refs
    return loc_by_name, deps_by_name


def def_closure(start, deps_by_name) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        name = stack.pop()
        if name in seen or name not in deps_by_name:
            continue
        seen.add(name)
        stack.extend(deps_by_name[name])
    return seen


# --- Main -----------------------------------------------------------------
def main() -> int:
    sort_key = "proof"
    as_csv = False
    for arg in sys.argv[1:]:
        if arg.startswith("--sort="):
            sort_key = arg.split("=", 1)[1]
        elif arg == "--csv":
            as_csv = True
        else:
            print(f"unknown argument: {arg}", file=sys.stderr)
            return 2

    imports, modules = build_import_graph()
    file_loc_cache: dict[str, int] = {}

    def file_loc(module: str) -> int:
        if module not in file_loc_cache:
            path = module_path(module)
            file_loc_cache[module] = (
                count_loc_text(open(path, encoding="utf-8").read())
                if os.path.exists(path) else 0
            )
        return file_loc_cache[module]

    exclude = set()
    for root in EXCLUDE_ROOTS:
        exclude |= import_closure([root], imports, modules)

    prog_loc, prog_deps = build_def_graph(CHECKER_FILES)

    rules = sorted(
        f[:-len(".lean")] for f in os.listdir(RULES_DIR) if f.endswith(".lean")
    )

    rows = []
    for rule in rules:
        module = f"Cpc.Proofs.Rules.{rule}"
        own = import_closure([module], imports, modules) - exclude
        proof = sum(file_loc(m) for m in own)

        prog_name = "__eo_prog_" + rule.lower()
        if prog_name in prog_deps:
            cl = def_closure(prog_name, prog_deps)
            prog = sum(prog_loc[n] for n in cl)
            prog_defs = len(cl)
        else:
            prog = 0
            prog_defs = 0
        rows.append((rule, proof, len(own), prog, prog_defs))

    keymap = {
        "proof": lambda r: (-r[1], r[0]),
        "prog": lambda r: (-r[3], r[0]),
        "name": lambda r: r[0],
    }
    if sort_key not in keymap:
        print(f"unknown sort key: {sort_key} (use proof|prog|name)", file=sys.stderr)
        return 2
    rows.sort(key=keymap[sort_key])

    if as_csv:
        print("rule,proof_loc,proof_files,eo_prog_loc,eo_prog_defs")
        for rule, proof, files, prog, defs in rows:
            print(f"{rule},{proof},{files},{prog},{defs}")
        return 0

    print("Per-proof-rule LOC  (PROOF excludes layers (a)-(c) + definitions;")
    print(" EO_PROG = __eo_prog_<rule> impl + transitive deps; neither is a partition)")
    print()
    print(f"{'RULE':40s} {'PROOF':>7s} {'files':>6s} {'EO_PROG':>8s} {'defs':>5s}")
    print("-" * 70)
    for rule, proof, files, prog, defs in rows:
        print(f"{rule:40s} {proof:7d} {files:6d} {prog:8d} {defs:5d}")
    print("-" * 70)
    proof_tot = sum(r[1] for r in rows)
    prog_tot = sum(r[3] for r in rows)
    n = len(rows)
    print(f"{'TOTAL (' + str(n) + ' rules, shared code double-counted)':40s} "
          f"{proof_tot:7d} {'':6s} {prog_tot:8d}")
    print(f"{'MEAN per rule':40s} {proof_tot // n:7d} {'':6s} {prog_tot // n:8d}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
