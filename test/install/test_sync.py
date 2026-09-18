#!/usr/bin/env python3
"""Exercise the real installers with a compiler whose output stays constant.

Run with python3 -B -m unittest discover -s test/install -v. No Ethos or Lean
build is needed: the fixture models signature edits erased by compilation.
All installs and checks run in a disposable repository.
"""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


REPO_ROOT = Path(__file__).resolve().parents[2]
ENTRY_POINTS = ("install-sig.sh", "install-cpc.sh")
STALE_MESSAGE = "is NOT up to date with"

DRIVER = r'''
from pathlib import Path
import sys

out = Path(sys.argv[sys.argv.index("--final-out-dir") + 1]) / "lean"
files = {
    "Logos.lean": "import Cpc.LogosTerm\npartial def checker := true\n",
    "LogosTerm.lean": "inductive UserOp where\n  | and : UserOp\n",
    "Parser.lean": "-- parser\n",
    "SmtEval.lean": "-- evaluator\n",
    "SmtModelDefs.lean": "-- model definitions\n",
    "SmtValueOrder.lean": "-- value order\n",
    "SmtModel.lean": "-- model\n",
    "Spec.lean": "-- (UserOp.and) => SmtTerm.and\n",
    "Proofs/RuleLemmas.lean": "-- rule lemmas\n",
    "Proofs/Rules/Refl.lean": "-- generated rule stub\n",
}
for name, content in files.items():
    if name == "Parser.lean" and "--no-parser" in sys.argv:
        continue
    path = out / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
'''


class SynchronizationTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="logos sync ")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.repo = self.root / "logos"
        install = self.repo / "install"
        (install / "defs").mkdir(parents=True)
        for script in ENTRY_POINTS:
            shutil.copy2(REPO_ROOT / "install" / script, install / script)
        (install / "defs" / "Cpc.eos").write_text("; fixture semantics\n")
        self.cache = install / "defs" / "Cpc.cached.eo"

        self.source = self.root / "signature" / "Cpc.eo"
        self.source.parent.mkdir()
        self.source.write_text(
            '; Source documentation\n(include "predicates.eo")\n'
            '(include "predicates.eo") ; shared include\n'
        )
        self.predicates = self.source.with_name("predicates.eo")
        self.predicates.write_text(
            "(declare-const $is_seq_const_rec (-> Int Int))\n"
            "(declare-const $is_seq_const (-> Int Int))\n"
        )

        self.ethos = self.root / "ethos"
        self.driver = self.ethos / "tools" / "eoc" / "driver.py"
        self.driver.parent.mkdir(parents=True)
        self.driver.write_text(DRIVER)
        self.tmp = self.root / "tmp"
        self.tmp.mkdir()
        self.env = dict(os.environ, TMPDIR=str(self.tmp))
        self.install()
        # Hand-written proofs must survive checks as well as real installs.
        (self.repo / "Cpc" / "Proofs" / "Rules" / "Refl.lean").write_text(
            "-- existing proof\n"
        )

    def invoke(self, script, *args):
        return subprocess.run(
            [
                "bash", str(self.repo / "install" / script),
                "--ethos", str(self.ethos),
                "--out-dir", str(self.root / "out"),
                *map(str, args),
            ],
            cwd=self.repo,
            env=self.env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=30,
        )

    def install(self, *args):
        result = self.invoke("install-sig.sh", self.source, *args)
        self.assertEqual(result.returncode, 0, result.stdout)

    def snapshot(self):
        return {
            str(path.relative_to(self.repo)): (
                path.read_bytes(), path.stat().st_mtime_ns, path.stat().st_mode
            )
            for path in self.repo.rglob("*") if path.is_file()
        }

    def check(self, script, *args, status=0, cached=False):
        before = self.snapshot()
        source = ["--cached"] if cached else [self.source]
        result = self.invoke(script, "--check", *source, *args)
        self.assertEqual(before, self.snapshot(), result.stdout)
        self.assertEqual(list(self.tmp.iterdir()), [], result.stdout)
        self.assertEqual(result.returncode, status, result.stdout)
        return result.stdout

    def change_signature(self):
        self.predicates.write_text(
            self.predicates.read_text().replace("(-> Int Int)", "(-> Int Bool)")
        )

    def assert_cache_drift(self, output, cache="install/defs/Cpc.cached.eo"):
        self.assertIn(STALE_MESSAGE, output)
        self.assertIn(cache, output)
        self.assertIn("cached signature", output)
        self.assertIn("1 file(s)", output)
        self.assertNotIn("  update  Cpc/", output)
        self.assertNotIn("  update  CpcMini/", output)

    def test_matching_cache(self):
        for script in ENTRY_POINTS:
            with self.subTest(script=script):
                self.check(script)

    def test_signature_drift_with_identical_generated_files(self):
        self.change_signature()
        for script in ENTRY_POINTS:
            with self.subTest(script=script):
                self.assert_cache_drift(self.check(script, status=1))

    def test_source_comment_only_changes(self):
        self.source.write_text("; New documentation\n\n" + self.source.read_text())
        self.predicates.write_text(
            self.predicates.read_text().replace("))", ")) ; return type")
            + "\n; More documentation\n"
        )
        for script in ENTRY_POINTS:
            with self.subTest(script=script):
                self.check(script)

    def test_missing_cache(self):
        self.cache.unlink()
        for script in ENTRY_POINTS:
            with self.subTest(script=script):
                self.assert_cache_drift(self.check(script, status=1))

    def test_flattening_failure(self):
        for source in ('(include "missing.eo")\n', '(reference "other.eo")\n'):
            self.source.write_text(source)
            for script in ENTRY_POINTS:
                with self.subTest(source=source, script=script):
                    output = self.check(script, status=1)
                    self.assertIn("could not flatten", output)
                    self.assertIn("install/defs/Cpc.cached.eo", output)
                    self.assertNotIn(STALE_MESSAGE, output)

    def test_cached_checks_do_not_reflatten(self):
        self.change_signature()
        for script in ENTRY_POINTS:
            with self.subTest(script=script):
                self.check(script, cached=True)

    def test_explicit_rules_do_not_require_cache(self):
        self.install("--mini")
        self.cache.unlink()
        for script in ENTRY_POINTS:
            for options in ((), ("--mini",)):
                with self.subTest(script=script, options=options):
                    self.check(script, *options, "--rules", "refl")

    def test_custom_package_does_not_require_cache(self):
        self.install("--package", "Mine")
        self.cache.unlink()
        self.check("install-sig.sh", "--package", "Mine")

    def test_mini_default_rules_check_cache(self):
        self.install("--mini")
        for script in ENTRY_POINTS:
            self.check(script, "--mini")
        self.check("install-cpc.sh", "--all")
        self.change_signature()
        for script in ENTRY_POINTS:
            with self.subTest(script=script):
                self.assert_cache_drift(self.check(script, "--mini", status=1))
        output = self.check("install-cpc.sh", "--all", status=1)
        self.assertEqual(output.count(STALE_MESSAGE), 2, output)

    def test_cache_override(self):
        alternate = self.repo / "alternate.eo"
        shutil.copy2(self.cache, alternate)
        self.cache.write_text("; stale default cache\n")
        for script in ENTRY_POINTS:
            self.check(script, "--cache", alternate)
        self.change_signature()
        for script in ENTRY_POINTS:
            with self.subTest(script=script):
                output = self.check(script, "--cache", alternate, status=1)
                self.assert_cache_drift(output, "alternate.eo")
                self.check(script, "--cache", alternate, cached=True)

    def test_generated_package_drift_still_fails(self):
        (self.repo / "Cpc" / "Logos.lean").write_text("-- stale checker\n")
        for script in ENTRY_POINTS:
            with self.subTest(script=script):
                output = self.check(script, status=1)
                self.assertIn(STALE_MESSAGE, output)
                self.assertIn("  update  Cpc/Logos.lean", output)

    def test_compilation_failure_is_not_reported_as_drift(self):
        self.driver.write_text('raise SystemExit("fixture compiler failure")\n')
        for script in ENTRY_POINTS:
            with self.subTest(script=script):
                output = self.check(script, status=1)
                self.assertIn("fixture compiler failure", output)
                self.assertNotIn(STALE_MESSAGE, output)


if __name__ == "__main__":
    unittest.main()
