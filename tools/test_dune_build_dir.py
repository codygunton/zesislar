"""Check stable Dune paths and the isolation of private build files."""

import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from dune_build_dir import ALIAS, canonical_command, physical_working_dir


class DuneBuildDirectoryTests(unittest.TestCase):
    def command(self, root, name="first"):
        physical = root / "_build/agents" / name
        return ["dune", "build", "--root", str(root), "--build-dir", str(physical)]

    def test_rewrites_only_the_inner_dune_option(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inner = self.command(root)
            command = ["python", "build_record.py", "--build-dir", "outer", "--",
                       "opam", "exec", "--", *inner]
            with canonical_command(command) as rewritten:
                self.assertEqual(rewritten[3], "outer")
                self.assertEqual(rewritten[-1], ALIAS)
                self.assertEqual((root / ALIAS).resolve(), Path(inner[-1]))
                self.assertEqual(command[-1], inner[-1])

    def test_dependency_wrapper_runs_after_opam_path_selection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            command = ["opam", "exec", "--", *self.command(root)]
            with canonical_command(command) as rewritten:
                self.assertEqual(rewritten[:3], command[:3])
                self.assertEqual(rewritten[5], "--execute")
                shim = Path(rewritten[6]) / "coqdep"
                self.assertTrue(shim.is_file())
                self.assertTrue(os.access(shim, os.X_OK))
                self.assertEqual(rewritten[7:9], ["dune", "build"])

    def test_equals_options_and_saved_physical_working_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = root / "_build/agents/first"
            command = ["dune", "build", "--root=" + str(root), "--build-dir=" + str(first)]
            with canonical_command(command) as rewritten:
                self.assertEqual(rewritten[-1], "--build-dir=" + ALIAS)
            logical = str(root / ALIAS / "default")
            with patch("dune_build_dir.active_dune", return_value=False):
                with canonical_command(self.command(root, "second")):
                    self.assertEqual(physical_working_dir(first, logical), str(first / "default"))

    def test_rejects_nonprivate_or_repeated_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for suffix in ["_build", "_build/agents", "outside"]:
                command = ["dune", "build", "--root", str(root), "--build-dir", str(root / suffix)]
                with self.assertRaisesRegex(ValueError, "private"):
                    with canonical_command(command):
                        self.fail("The command must not run.")
            command = self.command(root) + ["--build-dir=other"]
            with self.assertRaisesRegex(ValueError, "repeated"):
                with canonical_command(command):
                    self.fail("The command must not run.")

    def test_rejects_unowned_alias_and_live_retarget(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            alias = root / ALIAS
            alias.mkdir()
            with self.assertRaisesRegex(ValueError, "symlink"):
                with canonical_command(self.command(root)):
                    self.fail("The command must not run.")
            alias.rmdir()
            alias.symlink_to(root / "outside")
            with self.assertRaisesRegex(ValueError, "outside"):
                with canonical_command(self.command(root)):
                    self.fail("The command must not run.")
            alias.unlink()
            with canonical_command(self.command(root)):
                pass
            with patch("dune_build_dir.active_dune", return_value=True):
                with self.assertRaisesRegex(ValueError, "still uses"):
                    with canonical_command(self.command(root, "second")):
                        self.fail("The command must not run.")
            self.assertEqual(alias.resolve(), root / "_build/agents/first")

    def test_rejects_private_storage_outside_the_workspace(self):
        with tempfile.TemporaryDirectory() as directory:
            parent = Path(directory)
            root = parent / "workspace"
            (root / "_build").mkdir(parents=True)
            outside = parent / "outside"
            outside.mkdir()
            (root / "_build/agents").symlink_to(outside)
            with self.assertRaisesRegex(ValueError, "private"):
                with canonical_command(self.command(root)):
                    self.fail("The command must not run.")
            self.assertEqual(list(outside.iterdir()), [])

    def test_rejects_recipe_record_for_another_build(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            command = self.command(root)
            with canonical_command(command):
                pass
            physical = Path(command[-1])
            record = physical / "dune-build-dir.json"
            data = json.loads(record.read_text())
            data["physical_directory"] = str(root / "another")
            record.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "does not bind"):
                physical_working_dir(physical, str(root / ALIAS / "default"))

    def test_unrelated_command_remains_exact(self):
        command = ["python", "writer.py", "--build-dir", "/private"]
        with canonical_command(command) as rewritten:
            self.assertEqual(rewritten, command)


if __name__ == "__main__":
    unittest.main()
