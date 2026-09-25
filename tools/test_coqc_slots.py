"""Tests for machine-wide coqc slot sizing."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "det"))
import coqc_slots  # noqa: E402


class CoqcSlotsTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.proc = self.base / "proc"
        self.proc.mkdir()
        self.root = self.base / "worktree"
        self.root.mkdir()
        self.other = self.base / "other"
        self.other.mkdir()

    def add_process(self, pid: int, cwd: Path, name: str = "coqc"):
        process = self.proc / str(pid)
        process.mkdir()
        (process / "comm").write_text(name + "\n")
        (process / "cwd").symlink_to(cwd, target_is_directory=True)

    def test_launch_width_excludes_own_jobs_and_rechecks_other_jobs(self):
        self.add_process(1, self.root)
        self.add_process(2, self.root / "_build")
        (self.root / "_build").mkdir()
        self.add_process(3, self.other)
        self.add_process(4, self.other, "python3")
        self.assertEqual(coqc_slots.width(46, self.root, self.proc),
                         (32, 2, 1))
        self.add_process(5, self.other)
        self.assertEqual(coqc_slots.width(48, self.root, self.proc,
                                          maximum=3), (1, 2, 2))

    def test_drain_check_refuses_a_remaining_coqc(self):
        self.add_process(1, self.other)
        tool = Path(coqc_slots.__file__)
        command = [sys.executable, str(tool), str(self.root), "24",
                   "--proc", str(self.proc), "--drain-floor", "0"]
        failed = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(failed.returncode, 3)
        self.assertIn("drain incomplete: 1 coqc remain", failed.stderr)
        (self.proc / "1" / "comm").write_text("python3\n")
        passed = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(passed.returncode, 0)
        self.assertEqual(passed.stdout.strip(), "24 0 0")

    def test_base_root_excludes_nested_worktree_jobs(self):
        nested = self.root / ".worktrees" / "agent"
        nested.mkdir(parents=True)
        self.add_process(1, self.root)
        self.add_process(2, nested)
        self.assertEqual(coqc_slots.width(48, self.root, self.proc),
                         (32, 1, 1))

    def test_fair_share_applies_only_with_other_jobs(self):
        self.assertEqual(coqc_slots.width_from_counts(48, 20, 20),
                         (48, 20, 0))
        self.assertEqual(coqc_slots.width_from_counts(48, 21, 20),
                         (32, 20, 1))
        self.assertEqual(coqc_slots.width_from_counts(48, 35, 20),
                         (32, 20, 15))
        self.assertEqual(coqc_slots.width_from_counts(48, 40, 20),
                         (28, 20, 20))

    def test_unreadable_cwd_counts_as_other(self):
        process = self.proc / "1"
        process.mkdir()
        (process / "comm").write_text("coqc\n")
        self.assertEqual(coqc_slots.width(48, self.root, self.proc),
                         (32, 0, 1))


if __name__ == "__main__":
    unittest.main()
