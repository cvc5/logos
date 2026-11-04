#!/usr/bin/env python3
"""Audit the executable imports; optionally build with semantics absent."""

import argparse
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
ENTRIES = ("Main", "MainNative", "Cpc", "CpcMini")
SEMANTIC = {"SmtModel", "SmtModelDefs", "SmtValueOrder", "Spec", "ApiChecks", "ApiCorrect", "Proofs"}


def checker_sources():
    pending = list(ENTRIES)
    found = set()
    while pending:
        name = pending.pop()
        if name in found:
            continue
        parts = name.split(".")
        if parts[0] in {"Cpc", "CpcMini"} and set(parts[1:]) & SEMANTIC:
            raise SystemExit(f"error: checker imports semantic module {name}")
        path = ROOT / (name.replace(".", "/") + ".lean")
        if not path.is_file():
            if parts[0] not in {"Init", "Std", "Lean"}:
                raise SystemExit(f"error: checker imports external module {name}")
            continue
        found.add(name)
        # Module imports in this tree occupy a line each. Ignore documentation
        # examples, which can contain import lines inside block comments.
        source = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
        pending.extend(re.findall(r"^(?:public )?import (?:all )?([\w.]+)", source, re.M))
    return [Path(name.replace(".", "/") + ".lean") for name in sorted(found)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true")
    args = parser.parse_args()
    sources = checker_sources()
    print(f"Checker boundary: {len(sources)} source modules; no model semantics or external packages.", flush=True)
    if not args.build:
        return
    # The isolated tree deliberately contains neither verification sources nor
    # cached artifacts. A semantic import cannot accidentally succeed because
    # a previous proof build left an olean on the search path.
    with tempfile.TemporaryDirectory(prefix="logos-checker-boundary-") as temporary:
        dest = Path(temporary)
        for relative in sources + [Path("lakefile.toml"), Path("lake-manifest.json"), Path("lean-toolchain")]:
            target = dest / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / relative, target)
        subprocess.run(["lake", "build", "logos", "logos-native", "CpcMini"], cwd=dest, check=True)
        if (dest / ".lake/packages").exists() and any((dest / ".lake/packages").iterdir()):
            raise SystemExit("error: checker build acquired external packages")
    print("Checker builds with all model semantics and verification sources absent.")


if __name__ == "__main__":
    main()
