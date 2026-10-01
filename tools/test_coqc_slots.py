"""Tests for machine-wide coqc slot sizing."""

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "det"))
import coqc_slots  # noqa: E402


class CoqcSlotsTest(unittest.TestCase):
    def setUp(self):
        # Fixture expectations use 48 slots, independent of the active gate budget.
        from unittest.mock import patch
        environment = patch.dict(os.environ, {"ZESU_MAX_COQC": "48"})
        environment.start()
        self.addCleanup(environment.stop)
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

    def test_gate_drain_accepts_16_registered_writers_and_keeps_24_width(self):
        reservations = self.base / "reservations"
        reservations.mkdir()
        for pid in range(1, 17):
            self.add_process(pid, self.other)
            (reservations / f"{os.getpid()}.{pid}").write_text(
                f"{pid}\nwriter=writer-{(pid - 1) // 2}\n")
        tool = Path(coqc_slots.__file__)
        command = [sys.executable, str(tool), str(self.root), "24",
                   "--proc", str(self.proc), "--drain-floor", "0",
                   "--writer-reservations", str(reservations)]
        passed = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(passed.returncode, 0, passed.stderr)
        self.assertEqual(passed.stdout.strip(), "24 0 16")
        self.add_process(17, self.other)
        failed = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(failed.returncode, 3)
        self.assertIn("drain incomplete: 1 coqc remain", failed.stderr)

    def test_gate_slots_preserve_writer_reservation_without_live_writers(self):
        self.assertEqual(coqc_slots.width_from_counts(24, 9, 0,
                                                      writer_reserved=16), (23, 0, 9))
        self.assertEqual(coqc_slots.width_from_counts(24, 24, 0, writers=16,
                                                      writer_reserved=16), (24, 0, 24))

    def test_shell_coqc_wrapper_and_compiler_child_count_once(self):
        self.add_process(1, self.other)
        self.add_process(2, self.other)
        (self.proc / "1/exe").symlink_to("/bin/bash")
        (self.proc / "2/exe").symlink_to("/bin/sleep")
        (self.proc / "1/task/1").mkdir(parents=True)
        (self.proc / "1/task/1/children").write_text("2\n")
        reservations = self.base / "reservations"
        reservations.mkdir()
        (reservations / f"{os.getpid()}.tree").write_text("1\nwriter=tf2\n")
        snapshot = coqc_slots.compiler_pids(self.proc)
        self.assertEqual(snapshot, {2})
        self.assertEqual(coqc_slots.writer_pids(reservations, self.proc, snapshot), {2})
        self.assertEqual(coqc_slots.counts(self.root, self.proc), (1, 0))

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

    def store_command(self):
        store = self.base / "stores" / "own"
        store.mkdir(parents=True)
        alias = self.root / "build-store"
        alias.symlink_to(store, target_is_directory=True)
        reservations = self.base / "reservations"
        reservations.mkdir()
        command = [sys.executable, str(Path(coqc_slots.__file__)),
                   str(self.root), "24", "--proc", str(self.proc),
                   "--own-build-dir", str(alias),
                   "--writer-reservations", str(reservations)]
        return store, reservations, command

    def test_symlinked_own_store_keeps_24_slots(self):
        store, _, command = self.store_command()
        for pid in range(1, 25):
            self.add_process(pid, store)
        self.add_process(25, store)
        (self.proc / "25/exe").symlink_to("/bin/bash")
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "24 24 0")

    def test_adjacent_store_jobs_reduce_width(self):
        store, _, command = self.store_command()
        adjacent = store.parent / "other"
        adjacent.mkdir()
        for pid in range(1, 11):
            self.add_process(pid, adjacent)
        self.add_process(11, store)
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "22 1 10")
        self.assertLess(int(result.stdout.split()[0]), 24)

    def test_writer_in_own_store_uses_same_ownership_check(self):
        store, reservations, command = self.store_command()
        self.add_process(1, store)
        (reservations / f"{os.getpid()}.writer").write_text("1\nwriter=tf2\n")
        for pid in range(2, 11):
            self.add_process(pid, self.other)
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "23 1 9")

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
