#!/usr/bin/env python3
"""Isolated dummy-process tests. Never invokes Lean/Lake or the real lock root."""
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

WRAPPER = Path(__file__).resolve().with_name("build-slot-run.sh")
REAL_PS = shutil.which("ps")


class SlotSafety(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="v1-slot-safety-")
        self.base = Path(self.tmp.name)
        self.slots = self.base / "slots"
        self.slots.mkdir()
        self.children = []

    def tearDown(self):
        for p in self.children:
            if p.poll() is None:
                p.terminate()
        for p in self.children:
            try:
                p.communicate(timeout=8)
            except subprocess.TimeoutExpired:
                p.kill()
                p.communicate()
        self.tmp.cleanup()

    def start(self, cmd=None, maximum=1, extra=None):
        env = dict(os.environ, BUILD_SLOT_DIR=str(self.slots),
                   BUILD_SLOT_MAX=str(maximum), BUILD_SLOT_POLL="0.02",
                   BUILD_SLOT_OWNER_GRACE="0")
        if extra:
            env.update(extra)
        p = subprocess.Popen(["bash", str(WRAPPER)] + (cmd or ["true"]),
                             env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.children.append(p)
        return p

    def await_path(self, path):
        deadline = time.monotonic() + 6
        while not path.exists() and time.monotonic() < deadline:
            time.sleep(0.02)
        self.assertTrue(path.exists(), str(path))

    def finish(self, p, code=0):
        out, err = p.communicate(timeout=8)
        self.assertEqual(p.returncode, code, (out, err))

    def await_waiter(self):
        deadline = time.monotonic() + 6
        while not list(self.slots.glob(".waiting.*")) and time.monotonic() < deadline:
            time.sleep(0.02)
        self.assertTrue(list(self.slots.glob(".waiting.*")))

    def marker_command(self, name="ran"):
        return [sys.executable, "-c", "from pathlib import Path; import sys; Path(sys.argv[1]).touch()", str(self.base/name)]

    def dead_slot(self, phase=None):
        slot = self.slots / "slot-1"
        slot.mkdir()
        (slot/"pid").write_text("99999999\n")
        (slot/"started").write_text("dead-owner\n")
        (slot/"token").write_text("fixture\n")
        if phase:
            (slot/"phase").write_text(phase+"\n")
        return slot

    def fake_ps(self, mode):
        fakebin = self.base / "bin"
        fakebin.mkdir()
        script = fakebin/"ps"
        body = "#!/bin/sh\n"
        if mode == "failure":
            body += "exit 77\n"
        elif mode == "empty":
            body += "exit 0\n"
        elif mode == "after-first":
            body += 'if [ -e "$FAKE_PS_SEEN" ]; then exit 77; fi\n'
            body += ': > "$FAKE_PS_SEEN"\n'
            body += f'exec "{REAL_PS}" "$@"\n'
        script.write_text(body)
        script.chmod(0o755)
        return {"PATH":str(fakebin)+os.pathsep+os.environ["PATH"],
                "FAKE_PS_SEEN":str(self.base/"ps-seen")}

    def test_invalid_maximum(self):
        for maximum in [0, 4, 100, "bad"]:
            self.finish(self.start(maximum=maximum), 2)

    def test_child_exit_and_cleanup(self):
        self.finish(self.start(["bash", "-c", "exit 37"]), 37)
        self.assertEqual(list(self.slots.iterdir()), [])

    def test_fourth_waits_at_three(self):
        releases = []
        for i in range(3):
            entered = self.base/f"entered-{i}"
            release = self.base/f"release-{i}"
            releases.append(release)
            self.start([sys.executable, "-c",
                "from pathlib import Path; import sys,time; Path(sys.argv[1]).touch(); "
                "exec('while not Path(sys.argv[2]).exists(): time.sleep(0.02)')",
                str(entered), str(release)], maximum=3)
            self.await_path(entered)
        fourth = self.start(self.marker_command(), maximum=3)
        time.sleep(0.3)
        self.assertFalse((self.base/"ran").exists())
        releases[0].touch()
        self.finish(self.children[0])
        self.finish(fourth)
        for p, release in zip(self.children[1:3], releases[1:]):
            release.touch()
            self.finish(p)
        self.assertEqual(list(self.slots.iterdir()), [])

    def test_dead_owner_reclaimed(self):
        self.dead_slot()
        self.finish(self.start(self.marker_command()))
        self.assertTrue((self.base/"ran").exists())
        self.assertEqual(list(self.slots.iterdir()), [])

    def test_live_owner_not_reclaimed(self):
        slot = self.dead_slot()
        (slot/"pid").write_text(str(os.getpid())+"\n")
        stamp = subprocess.check_output([REAL_PS, "-p", str(os.getpid()), "-o", "lstart="], text=True).strip()
        (slot/"started").write_text(stamp+"\n")
        p = self.start(self.marker_command())
        self.await_waiter()
        time.sleep(0.3)
        self.assertFalse((self.base/"ran").exists())
        p.terminate()
        self.finish(p, 143)
        self.assertEqual((slot/"token").read_text(), "fixture\n")

    def test_reused_pid_different_start(self):
        slot = self.dead_slot()
        (slot/"pid").write_text(str(os.getpid())+"\n")
        self.finish(self.start(self.marker_command()))
        self.assertTrue((self.base/"ran").exists())

    def test_unknown_initializing_owner_not_reclaimed(self):
        (self.slots/"slot-1").mkdir()
        p = self.start(self.marker_command())
        self.await_waiter()
        time.sleep(0.3)
        self.assertFalse((self.base/"ran").exists())
        p.terminate()
        self.finish(p, 143)
        self.assertTrue((self.slots/"slot-1").is_dir())

    def test_unresolved_launch_not_reclaimed(self):
        self.dead_slot("launching")
        p = self.start(self.marker_command())
        self.await_waiter()
        time.sleep(0.3)
        self.assertFalse((self.base/"ran").exists())
        p.terminate()
        self.finish(p, 143)

    def test_ps_failure_does_not_start_or_reclaim(self):
        slot = self.dead_slot()
        self.finish(self.start(self.marker_command(), extra=self.fake_ps("failure")), 75)
        self.assertFalse((self.base/"ran").exists())
        self.assertEqual((slot/"token").read_text(), "fixture\n")

    def test_unresolved_running_not_reclaimed(self):
        slot = self.dead_slot("running")
        p = self.start(self.marker_command())
        self.await_waiter()
        time.sleep(0.3)
        self.assertFalse((self.base/"ran").exists())
        p.terminate()
        self.finish(p, 143)
        self.assertTrue(slot.is_dir())

    def test_empty_successful_ps_is_not_absence(self):
        slot = self.dead_slot()
        self.finish(self.start(self.marker_command(), extra=self.fake_ps("empty")), 75)
        self.assertFalse((self.base/"ran").exists())
        self.assertEqual((slot/"token").read_text(), "fixture\n")

    def test_ps_failure_inside_allocation_does_not_reclaim(self):
        slot = self.dead_slot()
        self.finish(self.start(self.marker_command(), extra=self.fake_ps("after-first")), 75)
        self.assertTrue((self.base/"ps-seen").exists())
        self.assertFalse((self.base/"ran").exists())
        self.assertEqual((slot/"token").read_text(), "fixture\n")
        self.assertFalse((self.slots/".allocation").exists())

    def test_pause_gate(self):
        pause = self.slots/".paused"
        pause.touch()
        p = self.start(self.marker_command())
        time.sleep(0.2)
        self.assertFalse((self.base/"ran").exists())
        pause.unlink()
        self.finish(p)

    def test_signal_forwarding_and_release(self):
        for sig, code in [(signal.SIGTERM, 143), (signal.SIGHUP, 129), (signal.SIGINT, 130)]:
            marker = self.base/f"child-{sig}"
            p = self.start([sys.executable, "-c",
                "import signal,time,sys; from pathlib import Path; "
                "signal.signal(signal.SIGINT, signal.SIG_DFL); "
                "Path(sys.argv[1]).touch(); time.sleep(30)", str(marker)])
            self.await_path(marker)
            p.send_signal(sig)
            self.finish(p, code)
            self.assertEqual(list(self.slots.iterdir()), [])

    def test_live_orphan_group_retains_slot(self):
        orphan = subprocess.Popen(["sleep", "30"], start_new_session=True)
        self.children.append(orphan)
        slot = self.dead_slot("running")
        (slot/"child").write_text(str(orphan.pid)+"\n")
        p = self.start(self.marker_command())
        time.sleep(0.3)
        self.assertFalse((self.base/"ran").exists())
        orphan.terminate()
        orphan.wait(timeout=3)
        self.finish(p)
        self.assertTrue((self.base/"ran").exists())


if __name__ == "__main__":
    unittest.main(verbosity=2)
