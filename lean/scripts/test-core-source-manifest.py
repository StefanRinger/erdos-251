#!/usr/bin/env python3
"""Isolated tests for core-source-manifest.py; fixtures live only in TemporaryDirectory."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().with_name("core-source-manifest.py")


class SourceManifestTests(unittest.TestCase):
    def write(self, root: Path, relative: str, content: str) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def run_tool(self, root: Path, *entries: str) -> subprocess.CompletedProcess[str]:
        command = [sys.executable, str(SCRIPT), "--root", str(root)]
        for entry in entries:
            command.extend(("--entry", entry))
        return subprocess.run(command, check=False, capture_output=True, text=True)

    def seed_metadata(self, root: Path) -> None:
        self.write(root, "lean-toolchain", "leanprover/lean4:v-test\n")
        self.write(root, "lake-manifest.json", "{}\n")
        self.write(root, "lakefile.toml", 'name = "fixture"\n')
        self.write(root, "PrimeGapNormality/ClassicalPNT/LICENSE", "fixture license\n")
        self.write(root, "PrimeGapNormality/ClassicalPNT/PROVENANCE.md", "fixture provenance\n")
        self.write(root, "PrimeGapNormality/ClassicalPNT/CITATION.upstream.cff", "fixture citation\n")

    def test_nested_comments_strings_external_and_hashes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            main_text = """/- import A.Ghost /- import A.NestedGhost -/ -/
import A.Dep Mathlib.Data.Nat
def message := "import A.StringGhost"
-- import A.LineGhost
"""
            self.write(root, "A/Main.lean", main_text)
            self.write(root, "A/Dep.lean", "import Std.Data.HashMap\n")

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 0, result.stderr)
            data = json.loads(result.stdout)
            self.assertEqual(data["entries"], ["A.Main"])
            self.assertEqual([item["path"] for item in data["sources"]], ["A/Dep.lean", "A/Main.lean"])
            self.assertEqual(
                {item["module"] for item in data["external_imports"]},
                {"Mathlib.Data.Nat", "Std.Data.HashMap"},
            )
            self.assertEqual(data["missing_local_imports"], [])
            expected = hashlib.sha256(main_text.encode("utf-8")).hexdigest()
            main_hash = next(item["sha256"] for item in data["sources"] if item["path"] == "A/Main.lean")
            self.assertEqual(main_hash, expected)
            citation = next(item for item in data["pnt_license_provenance"]
                            if item["path"].endswith("CITATION.upstream.cff"))
            self.assertEqual(citation["status"], "present")
            self.assertEqual(citation["sha256"],
                             hashlib.sha256(b"fixture citation\n").hexdigest())
            self.assertNotIn(str(root), result.stdout)

    def test_missing_local_import_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(root, "A/Main.lean", "import A.Missing\n")

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 2)
            data = json.loads(result.stdout)
            self.assertEqual(data["missing_local_imports"][0]["module"], "A.Missing")
            self.assertEqual(data["missing_local_imports"][0]["path"], "A/Missing.lean")

    def test_unterminated_nested_comment_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(root, "A/Main.lean", "/- outer /- nested -/\n")

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 2)
            data = json.loads(result.stdout)
            self.assertEqual(data["parse_issues"][0]["reason"], "unterminated block comment")

    def test_symlink_escape_is_not_followed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory)
            root = fixture / "repo"
            root.mkdir()
            self.seed_metadata(root)
            outside = fixture / "outside.lean"
            outside.write_text("def escaped := True\n", encoding="utf-8")
            (root / "A").mkdir()
            (root / "A" / "Escape.lean").symlink_to(outside)

            result = self.run_tool(root, "A.Escape")
            self.assertEqual(result.returncode, 2)
            data = json.loads(result.stdout)
            self.assertEqual(data["sources"], [])
            self.assertEqual(data["path_issues"][0]["reason"], "symlink/path escape")
            self.assertNotIn(str(fixture), result.stdout)

    def test_metadata_parent_symlink_escape_is_not_hashed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory)
            root = fixture / "repo"
            root.mkdir()
            self.write(root, "lean-toolchain", "leanprover/lean4:v-test\n")
            self.write(root, "lake-manifest.json", "{}\n")
            self.write(root, "lakefile.toml", 'name = "fixture"\n')
            self.write(root, "A/Main.lean", "import Mathlib.Data.Nat\n")

            outside = fixture / "outside-pnt"
            outside.mkdir()
            (outside / "LICENSE").write_text("outside license\n", encoding="utf-8")
            (outside / "PROVENANCE.md").write_text("outside provenance\n", encoding="utf-8")
            (outside / "CITATION.upstream.cff").write_text("outside citation\n", encoding="utf-8")
            (root / "PrimeGapNormality").mkdir()
            (root / "PrimeGapNormality" / "ClassicalPNT").symlink_to(outside, target_is_directory=True)

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 2)
            data = json.loads(result.stdout)
            self.assertEqual(len(data["metadata_path_issues"]), 3)
            self.assertTrue(all(item["reason"] == "symlink/path escape" for item in data["metadata_path_issues"]))
            self.assertTrue(all(item["status"] == "unsafe" for item in data["pnt_license_provenance"]))
            self.assertTrue(all("sha256" not in item for item in data["pnt_license_provenance"]))
            self.assertNotIn(str(fixture), result.stdout)

    def test_dependency_first_order_on_diamond(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(root, "A/Main.lean", "import A.Left A.Right\n")
            self.write(root, "A/Left.lean", "import A.Shared\n")
            self.write(root, "A/Right.lean", "import A.Shared\n")
            self.write(root, "A/Shared.lean", "import Mathlib.Data.Nat\n")

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 0, result.stderr)
            data = json.loads(result.stdout)
            self.assertEqual(
                data["project_build_order"],
                ["A.Shared", "A.Left", "A.Right", "A.Main"],
            )
            self.assertNotIn("Mathlib.Data.Nat", data["project_build_order"])
            self.assertEqual(data["import_cycles"], [])

    def test_multiple_entries_are_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(root, "A/First.lean", "import A.Shared\n")
            self.write(root, "A/Second.lean", "import A.Shared\n")
            self.write(root, "A/Shared.lean", "def shared := True\n")

            first = self.run_tool(root, "A.Second", "A.First", "A.Second")
            second = self.run_tool(root, "A.First", "A.Second")
            self.assertEqual(first.returncode, 0, first.stderr)
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertEqual(first.stdout, second.stdout)
            data = json.loads(first.stdout)
            self.assertEqual(data["entries"], ["A.First", "A.Second"])
            self.assertEqual(
                data["project_build_order"],
                ["A.Shared", "A.First", "A.Second"],
            )

    def test_import_cycle_is_explicit_and_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.seed_metadata(root)
            self.write(root, "A/Main.lean", "import A.Middle\n")
            self.write(root, "A/Middle.lean", "import A.Main\n")

            result = self.run_tool(root, "A.Main")
            self.assertEqual(result.returncode, 2)
            data = json.loads(result.stdout)
            self.assertEqual(data["project_build_order"], [])
            self.assertEqual(data["import_cycles"][0]["modules"], ["A.Main", "A.Middle"])
            self.assertEqual(
                data["import_cycles"][0]["edges"],
                [
                    {"from": "A.Main", "to": "A.Middle"},
                    {"from": "A.Middle", "to": "A.Main"},
                ],
            )


if __name__ == "__main__":
    unittest.main()
