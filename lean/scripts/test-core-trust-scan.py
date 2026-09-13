#!/usr/bin/env python3
"""Isolated TemporaryDirectory fixtures for core-trust-scan.py."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().with_name("core-trust-scan.py")


class CoreTrustScanTests(unittest.TestCase):
    def write(self, root: Path, relative: str, content: str) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def seed_metadata(self, root: Path) -> None:
        self.write(root, "lean-toolchain", "leanprover/lean4:v-test\n")
        self.write(root, "lake-manifest.json", "{}\n")
        self.write(root, "lakefile.toml", 'name = "fixture"\n')
        self.write(root, "PrimeGapNormality/ClassicalPNT/LICENSE", "fixture license\n")
        self.write(root, "PrimeGapNormality/ClassicalPNT/PROVENANCE.md", "fixture provenance\n")
        self.write(root, "PrimeGapNormality/ClassicalPNT/CITATION.upstream.cff", "fixture citation\n")

    def run_tool(self, root: Path, *entries: str) -> subprocess.CompletedProcess[str]:
        command = [sys.executable, str(SCRIPT), "--root", str(root)]
        for entry in entries:
            command.extend(("--entry", entry))
        return subprocess.run(command, check=False, capture_output=True, text=True)

    def test_comments_strings_identifiers_and_recursive_imports_are_clean(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(
                root,
                "A/Main.lean",
                """/- axiom hidden : False /- sorry admit -/ -/
import A.Dep
def quoted := "unsafe axiom sorry #eval 1"
def sorry_free := True
#print axioms sorry_free
set_option maxHeartbeats 100 in
example : True := by trivial
""",
            )
            self.write(root, "A/Dep.lean", "import A.Leaf\n")
            self.write(root, "A/Leaf.lean", "-- native_decide\ndef leaf := True\n")

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 0, result.stderr)
            data = json.loads(result.stdout)
            self.assertEqual(data["entries"], ["A.Main"])
            self.assertEqual([item["path"] for item in data["sources"]],
                             ["A/Dep.lean", "A/Leaf.lean", "A/Main.lean"])
            self.assertEqual(data["risky_occurrences"], [])
            self.assertEqual(data["unknown_option_occurrences"], [])
            self.assertEqual(data["set_option_occurrences"][0]["name"], "maxHeartbeats")
            self.assertNotIn(str(root), result.stdout)

    def test_actual_risky_commands_and_tokens_are_reported(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(
                root,
                "A/Main.lean",
                """@[fixture] axiom attributed : True
axiom assumed : True
theorem unfinished : True := by sorry
theorem admitted : True := by admit
#check Lean.sorryAx
#check Lean.admitAx
#check Lean.syntheticOpaque
#check Lean.ofReduceBool
unsafe def unchecked := 1
extern "fixture_symbol" opaque foreign : Nat
@[implemented_by unchecked] opaque replacement : Nat
example : True := by native_decide
#eval 1
#reduce 1 + 1
""",
            )

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 1, result.stderr)
            data = json.loads(result.stdout)
            tokens = {item["token"] for item in data["risky_occurrences"]}
            self.assertTrue(
                {"axiom", "sorry", "admit", "sorryAx", "admitAx",
                 "syntheticOpaque", "ofReduceBool", "unsafe", "extern",
                 "implemented_by", "native_decide", "#eval", "#reduce"}.issubset(tokens)
            )

    def test_benign_unknown_and_trust_sensitive_options_are_distinguished(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(
                root,
                "A/Main.lean",
                """set_option maxHeartbeats 10 in
example : True := by trivial
set_option fixture.unknownOption true in
example : True := by trivial
set_option debug.skipKernelTC true in
example : True := by trivial
""",
            )

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 1, result.stderr)
            data = json.loads(result.stdout)
            classes = {item["name"]: item["classification"] for item in data["set_option_occurrences"]}
            self.assertEqual(classes["maxHeartbeats"], "known-project-option")
            self.assertEqual(classes["fixture.unknownOption"], "unknown-to-static-allowlist")
            self.assertEqual(classes["debug.skipKernelTC"], "trust-sensitive")

    def test_missing_and_invalid_imports_use_manifest_failures(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(root, "A/Main.lean", "import A.Missing Bad-Token\n/- unterminated\n")

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 2)
            data = json.loads(result.stdout)
            self.assertEqual(data["closure_issues"]["missing_local_imports"][0]["module"], "A.Missing")
            self.assertEqual(data["closure_issues"]["parse_issues"][0]["token"], "Bad-Token")
            self.assertIn("unterminated block comment",
                          {item["reason"] for item in data["closure_issues"]["parse_issues"]})

    def test_import_cycle_is_reported_as_a_closure_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(root, "A/Main.lean", "import A.Dep\n")
            self.write(root, "A/Dep.lean", "import A.Main\n")
            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 2, result.stderr)
            data = json.loads(result.stdout)
            self.assertEqual(data["closure_issues"]["import_cycles"][0]["modules"],
                             ["A.Dep", "A.Main"])
            self.assertEqual(data["risky_occurrences"], [])

    def test_symlink_escape_is_not_scanned(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory)
            root = fixture / "repo"
            root.mkdir()
            self.seed_metadata(root)
            outside = fixture / "outside.lean"
            outside.write_text("axiom escaped : False\n", encoding="utf-8")
            (root / "A").mkdir()
            (root / "A" / "Escape.lean").symlink_to(outside)

            result = self.run_tool(root, "A.Escape")
            self.assertEqual(result.returncode, 2)
            data = json.loads(result.stdout)
            self.assertEqual(data["sources"], [])
            self.assertEqual(data["risky_occurrences"], [])
            self.assertEqual(data["closure_issues"]["path_issues"][0]["reason"], "symlink/path escape")
            self.assertNotIn(str(fixture), result.stdout)


if __name__ == "__main__":
    unittest.main()
