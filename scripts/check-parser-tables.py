#!/usr/bin/env python3
"""Check a generated parser configuration against the generated signature.

`Cpc/Parser.lean` is auto-generated from the same Eunoia signature as
`Cpc/Logos.lean`.  This script re-derives from the signature the facts the
generator has to get right, and fails if the parser table disagrees:

  * every operator of the signature is represented by at least one surface
    declaration;
  * a surface name does not represent the same operator more than once;
  * every proof rule of the calculus is named exactly once;
  * `__eo_typeof` inspects the value of an applied argument only where the parser
    keeps it: types and binder lists (`placeholder`, `Logos/Parser/Datatypes.lean`).

An operator may occur under more than one surface name.  In particular, a
signature `define` introduces an alias whose generated parser entry references
the same internal operator as its original declaration.

Surface arities such as Eunoia's `:arg-list` are explicit declaration metadata;
they cannot be reconstructed from the generated term types and are exercised by
the generic parser tests instead.

Usage: scripts/check-parser-tables.py [Cpc ...]
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def inductive_constructors(source: str, name: str) -> list[str]:
    """The constructor names of `inductive <name>`, in declaration order."""
    start = source.index(f"inductive {name} : Type where")
    body = source[start:]
    body = body[: body.index("deriving")]
    return re.findall(r"^\s*\|\s*([A-Za-z_0-9]+)\s*:", body, re.M)


def parser_entries(source: str) -> list[dict]:
    """The operator declarations of a generated parser table."""
    start = source.index("private def parserOps")
    table = source[start : source.index("/-- The proof rules of the calculus")]
    entries = []
    for chunk in table.split("\n  { name := ")[1:]:
        name = re.match(r'"((?:[^"\\]|\\.)*)"', chunk).group(1)
        # `arity` may itself mention helper operators, so only `build` says what
        # is declared by this entry.
        build = chunk.split("build :=", 1)[1] if "build :=" in chunk else ""
        entries.append(
            {
                "name": name,
                "ops": re.findall(r"\b(UserOp[123]?\.[A-Za-z_0-9]+)", build),
            }
        )
    return entries


# Operators whose typing equation uses an applied argument itself rather than only
# its type, with the positions of those arguments.  The parser keeps these
# arguments when it types a term, because they are types or binder lists.
VALUE_TYPED_ARGS = {
    ("UserOp._at__at_TypedList_nil", 0),  # a type
    ("UserOp.lambda", 0),  # a binder list
}


def check_typeof(logos_src: str) -> list[str]:
    """Check which applied arguments `__eo_typeof` uses other than by their type."""
    errors: list[str] = []
    body = logos_src.split("def __eo_typeof : Term -> Term\n", 1)[1]
    checked = 0
    for line in body.split("\n"):
        if not line.startswith("  | "):
            break
        if not line.startswith("  | (Term.Apply"):
            continue
        lhs, rhs = line[4:].split(" => ", 1)
        # Unwind `(Term.Apply (Term.Apply head a) b)`; arguments are variables.
        args: list[str] = []
        while m := re.fullmatch(r"\(Term\.Apply (.*) (__eo_\w+)\)", lhs):
            lhs, arg = m.groups()
            args.insert(0, arg)
        ops = re.findall(r"UserOp[123]?\.\w+", lhs)
        head = ops[0] if ops else lhs
        if "Term.Apply" in lhs or len(ops) > 1:
            errors.append(f"__eo_typeof matches on an argument's value: {line.strip()}")
            continue
        checked += 1
        values = re.sub(r"\(__eo_typeof __eo_\w+\)", "", rhs)
        for i, arg in enumerate(args):
            if re.search(rf"\b{arg}\b", values) and (head, i) not in VALUE_TYPED_ARGS:
                errors.append(f"__eo_typeof inspects the value of argument {i} of {head}")
    if checked == 0:
        errors.append("no application equations of __eo_typeof found")
    return errors


def check(calculus: str) -> list[str]:
    errors: list[str] = []
    term_src = (REPO_ROOT / calculus / "LogosTerm.lean").read_text()
    logos_src = (REPO_ROOT / calculus / "Logos.lean").read_text()
    parser_src = (REPO_ROOT / calculus / "Parser.lean").read_text()

    # 1. Operator coverage.
    declared: list[str] = []
    for family in ["UserOp", "UserOp1", "UserOp2", "UserOp3"]:
        # `None` is the generator's placeholder for a family with no members, so
        # it has no surface syntax and no entry in the parser table.
        declared += [
            f"{family}.{c}" for c in inductive_constructors(term_src, family) if c != "None"
        ]
    entries = parser_entries(parser_src)
    referenced = Counter(op for entry in entries for op in entry["ops"])
    for op in declared:
        if referenced[op] == 0:
            errors.append(f"operator {op} is not declared in the parser table")
    for op in referenced:
        if op not in declared:
            errors.append(f"parser table declares {op}, which the signature does not")

    # Definitions legitimately give one internal operator several surface
    # names.  Repeating the same surface-name/operator pair, however, is not an
    # alias and indicates that the generator emitted the same entry twice.
    surface_references = Counter(
        (entry["name"], op) for entry in entries for op in entry["ops"]
    )
    for (name, op), count in surface_references.items():
        if count > 1:
            errors.append(f"surface operator {name} declares {op} {count} times")

    # 2. Rule coverage.
    rules = inductive_constructors(logos_src, "CRule")
    table = parser_src[parser_src.index("private def parserRules") :]
    table = table[: table.index("\n]")]
    named = Counter(c for _, c in re.findall(r'\("([^"]+)",\s*\.([A-Za-z_0-9]+)\)', table))
    for rule in rules:
        if named[rule] == 0:
            errors.append(f"rule {rule} is not named in the parser table")
        elif named[rule] > 1:
            errors.append(f"rule {rule} is named {named[rule]} times")
    for rule in named:
        if rule not in rules:
            errors.append(f"parser table names rule {rule}, which the calculus does not have")

    # 3. Argument values used in typing.
    errors += check_typeof(logos_src)

    return errors


def main(argv: list[str]) -> int:
    calculi = argv[1:] or ["Cpc"]
    status = 0
    for calculus in calculi:
        errors = check(calculus)
        if errors:
            status = 1
            print(f"{calculus}/Parser.lean disagrees with the signature:", file=sys.stderr)
            for error in errors:
                print(f"  {error}", file=sys.stderr)
        else:
            print(f"{calculus}/Parser.lean agrees with the signature.")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
