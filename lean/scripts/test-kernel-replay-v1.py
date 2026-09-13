"""Isolated launcher tests with fake commands; never starts Lean or real slots."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


class ReplayLauncherTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copyfile(Path(__file__).with_name("kernel-replay.sh"), scripts / "kernel-replay.sh")
        (scripts / "build-slot-run.sh").write_text('#!/bin/bash\nexec "$@"\n')
        commands = self.root / "commands"
        commands.mkdir()
        python_stub = commands / "python3"
        python_stub.write_text(f'#!{sys.executable}\n' + '''import json, os, pathlib, sys
if "trust" in sys.argv[1]:
    print("{}")
    sys.exit(int(os.environ.get("TRUST_EXIT", "0")))
p=pathlib.Path("counter")
n=int(p.read_text())+1 if p.exists() else 1
p.write_text(str(n))
print(json.dumps({"hash": "changed" if n>1 and os.environ.get("CHANGE") else "stable"}))
''')
        lake_stub = commands / "lake"
        lake_stub.write_text(f'#!{sys.executable}\n' + '''import json, os, pathlib, sys
p=pathlib.Path("lake_calls")
with p.open("a") as f: f.write(json.dumps(sys.argv[1:])+"\\n")
if sys.argv[1]=="env":
    print("fake replay")
    sys.exit(int(os.environ.get("REPLAY_EXIT", "0")))
sys.exit(int(os.environ.get("FRESHNESS_EXIT", "0")))
''')
        python_stub.chmod(0o755)
        lake_stub.chmod(0o755)
        self.env = dict(os.environ, PATH=str(commands) + os.pathsep + os.environ["PATH"])

    def run_case(self, **extra):
        return subprocess.run(["bash", "scripts/kernel-replay.sh"], cwd=self.root,
                              env=dict(self.env, **extra), text=True, capture_output=True)

    def test_success_and_exact_fresh_target(self):
        result = self.run_case()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("PASS:", result.stdout)
        calls = (self.root / "lake_calls").read_text()
        self.assertIn('"leanchecker", "--fresh", "--verbose", "PrimeGapNormality.PaperAudit"', calls)
        self.assertEqual(len(list(self.root.rglob("finished_utc.txt"))), 1)

    def test_replay_failure_survives_tee(self):
        result = self.run_case(REPLAY_EXIT="17")
        self.assertEqual(result.returncode, 17)
        self.assertNotIn("PASS:", result.stdout)
        self.assertEqual(next(self.root.rglob("kernel_exit.txt")).read_text(), "17\n")

    def test_stale_build_stops_before_replay(self):
        result = self.run_case(FRESHNESS_EXIT="12")
        self.assertEqual(result.returncode, 12)
        self.assertNotIn("leanchecker", (self.root / "lake_calls").read_text())

    def test_trust_failure_stops_before_lake(self):
        result = self.run_case(TRUST_EXIT="9")
        self.assertEqual(result.returncode, 9)
        self.assertFalse((self.root / "lake_calls").exists())

    def test_changed_sources_not_passed(self):
        result = self.run_case(CHANGE="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn("PASS:", result.stdout)
        self.assertEqual(list(self.root.rglob("finished_utc.txt")), [])


if __name__ == "__main__": unittest.main()
