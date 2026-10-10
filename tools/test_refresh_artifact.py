"""Check private refresh admission without starting Dune or a compiler."""

import fcntl
import os
import shutil
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import refresh_artifact as refresh


class PrivateRefresh(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.build = self.root / "_build/agents/test"

    def test_one_target_uses_batch_and_private_build(self):
        args = refresh.command(self.root, self.build, "default/Test.vo", "/pinned")
        self.assertEqual(args[1:4], ["batch", "artifact-refresh", "--"])
        self.assertIn(str(self.build), args)
        self.assertIn("-j1", args)
        self.assertEqual(args[-1], "Test.vo")
        self.assertNotIn("locked", args)

    def test_default_context_targets_use_source_relative_dune_rules(self):
        args = refresh.command(self.root, self.build, "default/ZesuSsz/Automation/All.vo", "/pinned")
        self.assertEqual(args[-1], "ZesuSsz/Automation/All.vo")
        args = refresh.command(self.root, self.build, "ZesuSsz/Automation/All.vo", "/pinned")
        self.assertEqual(args[-1], "ZesuSsz/Automation/All.vo")
        with self.assertRaises(ValueError):
            refresh.command(self.root, self.build, "install/default/lib/plugin/META", "/pinned")

    def test_real_dune_rules_accept_the_source_relative_theory_target(self):
        switch = Path.home() / "islaris"
        if shutil.which("opam") is None or not switch.is_dir():
            self.skipTest("The pinned Dune toolchain is not installed.")
        parent = refresh.ROOT / "_build/agents"
        parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="refresh-rules-", dir=parent) as temporary:
            build = Path(temporary)
            args = refresh.command(refresh.ROOT, build, "default/ZesuSsz/Automation/Hooks.vo", str(switch))
            query = ["opam", "exec", "--switch=" + str(switch), "--", "dune", "rules",
                     "--root", str(refresh.ROOT), "--build-dir", str(build), args[-1]]
            result = subprocess.run(query, cwd=refresh.ROOT, env=refresh.environment(),
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("Hooks.v", result.stdout)
            self.assertIn("coqc", result.stdout)

    def test_shared_build_and_escaping_targets_are_rejected(self):
        for build in ("_build/default", "_build/agents", "../other"):
            with self.subTest(build=build), self.assertRaises(ValueError):
                refresh.build_path(self.root, build)
        for target in ("", ".", "./", "default", "default/", "default/.", "./default",
                       "@all", "-j48", "/tmp/Test.vo", "../Test.vo"):
            with self.subTest(target=target), self.assertRaises(ValueError):
                refresh.command(self.root, self.build, target, "/pinned")

    def test_inherited_admission_and_findlib_overrides_are_removed(self):
        with patch.dict(os.environ, {"ZESU_IN_GATE": "1", "ZESU_WRITER_ID": "writer",
                                    "ROCQ_COQC_BINARY": "other", "COQC_WRAPPER": "other",
                                    "OCAMLPATH": "/other/private"}):
            env = refresh.environment()
        for key in ("ZESU_IN_GATE", "ZESU_WRITER_ID", "ROCQ_COQC_BINARY", "COQC_WRAPPER", "OCAMLPATH"):
            self.assertNotIn(key, env)
        self.assertEqual(env["ZESU_IO"], "batch")

    def test_pet_before_lock_prevents_launch(self):
        with patch.object(refresh, "admission", return_value=False), patch.object(refresh.subprocess, "run") as run:
            self.assertIsNone(refresh.attempt(self.root, self.build, ["fake"], {}))
        run.assert_not_called()
        self.assertFalse(refresh.artifact_lock(self.build).exists())

    def test_changed_admission_inside_lock_releases_the_lock(self):
        with patch.object(refresh, "admission", side_effect=[True, False]), patch.object(refresh.subprocess, "run") as run:
            self.assertIsNone(refresh.attempt(self.root, self.build, ["fake"], {}))
        run.assert_not_called()
        with refresh.artifact_lock(self.build).open("a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            fcntl.flock(lock, fcntl.LOCK_UN)

    def test_busy_private_lock_does_not_request_a_gate(self):
        self.build.parent.mkdir(parents=True)
        with refresh.artifact_lock(self.build).open("a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            with patch.object(refresh, "admission", return_value=True), patch.object(refresh.subprocess, "run") as run:
                self.assertIsNone(refresh.attempt(self.root, self.build, ["fake"], {}))
            run.assert_not_called()

    def test_independent_build_does_not_wait_for_another_private_lock(self):
        self.build.parent.mkdir(parents=True)
        other = self.build.with_name("independent")
        with refresh.artifact_lock(self.build).open("a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            with patch.object(refresh, "admission", return_value=True), patch.object(refresh.subprocess, "run") as run:
                run.return_value.returncode = 0
                self.assertEqual(refresh.attempt(self.root, other, ["fake"], {}), 0)
            run.assert_called_once_with(["fake"], cwd=self.root, env={})

    def test_success_and_failure_release_the_private_lock(self):
        for status in (0, 2):
            with self.subTest(status=status):
                with patch.object(refresh, "admission", return_value=True), patch.object(refresh.subprocess, "run") as run:
                    run.return_value.returncode = status
                    self.assertEqual(refresh.attempt(self.root, self.build, ["fake"], {}), status)
                run.assert_called_once_with(["fake"], cwd=self.root, env={})
                with refresh.artifact_lock(self.build).open("a+") as lock:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    fcntl.flock(lock, fcntl.LOCK_UN)

    def test_pet_workspace_check_uses_cwd_only(self):
        proc = self.root / "proc"
        entry = proc / "123"
        entry.mkdir(parents=True)
        foreign = self.root.with_name(self.root.name + "-foreign")
        foreign.mkdir()
        self.addCleanup(foreign.rmdir)
        cwd = entry / "cwd"
        pet = {"pid": 123, "comm": "pet"}
        for directory, expected in ((foreign, False), (self.root, True), (self.build, True)):
            directory.mkdir(parents=True, exist_ok=True)
            cwd.symlink_to(directory)
            with self.subTest(directory=directory):
                self.assertEqual(refresh.pet_uses_workspace(pet, self.root, self.build, proc), expected)
            cwd.unlink()

    def test_foreign_pet_does_not_block_private_refresh(self):
        with patch.object(refresh, "inventory", return_value=[{"pid": 1, "comm": "pet"}]), \
                patch.object(refresh, "pet_uses_workspace", return_value=False), \
                patch.object(refresh, "query", side_effect=["none", "no gate lock"]):
            self.assertTrue(refresh.admission("fake", self.root, self.build, {}))

    def test_owned_pet_blocks_private_refresh(self):
        with patch.object(refresh, "inventory", return_value=[{"pid": 1, "comm": "pet"}]), \
                patch.object(refresh, "pet_uses_workspace", return_value=True), \
                patch.object(refresh, "query") as query:
            self.assertFalse(refresh.admission("fake", self.root, self.build, {}))
        query.assert_not_called()

    def test_pet_and_compiler_limit_preserve_normal_holds(self):
        with patch.object(refresh, "inventory", return_value=[{"pid": 1, "comm": "pet"}]), \
                patch.object(refresh, "pet_uses_workspace", return_value=True):
            self.assertFalse(refresh.admission("fake", self.root, self.build, {}))
        with patch.object(refresh, "inventory", return_value=[{"comm": "coqc"}] * 48):
            self.assertFalse(refresh.admission("fake", self.root, self.build, {}))
        for hold, gate, allowed in (("memory", "no gate lock", False), ("none", "state=wanted", False),
                                    ("none", "state=held", False), ("none", "no gate lock", True)):
            with self.subTest(hold=hold, gate=gate), patch.object(refresh, "inventory", return_value=[]), \
                    patch.object(refresh, "query", side_effect=[hold, gate]):
                self.assertEqual(refresh.admission("fake", self.root, self.build, {}), allowed)


if __name__ == "__main__":
    unittest.main()
