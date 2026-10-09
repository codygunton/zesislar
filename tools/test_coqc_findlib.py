"""Check private findlib records and compiler routing without Rocq execution."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from coqc_findlib import (RECORD_NAME, compiler_environment,
                         record_dune_environment)
from test_guard import fixture_environment


TOOLS = Path(__file__).resolve().parent


class CompilerFindlibTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "dune-project").write_text("(lang dune 3.17)\n")
        self.build = self.root / "_build/agents/private"
        self.tools = self.build / "default/tools"
        self.tools.mkdir(parents=True)
        (self.root / "_build/default").symlink_to(self.build / "default", target_is_directory=True)
        self.library = self.build / "install/default/lib"
        self.library.mkdir(parents=True)
        self.record = self.build / RECORD_NAME

    def write_record(self):
        return record_dune_environment(self.tools, {"OCAMLPATH": str(self.library),
                                                    "UNRELATED": "excluded"})

    def test_dune_value_replaces_ambient_private_value(self):
        self.write_record()
        environment = compiler_environment(self.root, {"OCAMLPATH": "/another/private/lib", "OTHER": "kept"})
        self.assertEqual(environment, {"OCAMLPATH": str(self.library), "OTHER": "kept"})
        record = json.loads(self.record.read_text())
        self.assertEqual(set(record), {"schema_version", "workspace", "private_build", "OCAMLPATH"})
        self.assertEqual(record["workspace"], str(self.root))
        self.assertEqual(record["private_build"], str(self.build))

    def test_missing_private_record_preserves_ambient_environment(self):
        for environment in ({}, {"OCAMLPATH": "/ambient/private/lib", "OTHER": "kept"}):
            with self.subTest(environment=environment):
                self.assertEqual(compiler_environment(self.root, environment), environment)
                self.assertFalse(self.record.exists())

    def test_no_private_build_preserves_ordinary_environment(self):
        (self.root / "_build/default").unlink()
        environment = {"OCAMLPATH": "/ordinary/lib", "OTHER": "kept"}
        self.assertEqual(compiler_environment(self.root, environment), environment)

    def test_record_is_idempotent_and_rejects_changed_environment(self):
        self.write_record()
        original = self.record.read_bytes()
        self.write_record()
        self.assertEqual(self.record.read_bytes(), original)
        with self.assertRaisesRegex(ValueError, "record changed"):
            record_dune_environment(self.tools, {"OCAMLPATH": "/different/lib"})
        self.assertEqual(self.record.read_bytes(), original)

    def test_malformed_record_is_rejected(self):
        self.record.write_text("not JSON")
        with self.assertRaisesRegex(ValueError, "malformed"):
            compiler_environment(self.root, {})

    def test_workspace_build_and_schema_mismatches_are_rejected(self):
        self.write_record()
        original = json.loads(self.record.read_text())
        for field, value in (("workspace", "/another/workspace"),
                             ("private_build", "/another/build"),
                             ("schema_version", True),
                             ("schema_version", 2),
                             ("OCAMLPATH", None)):
            with self.subTest(field=field, value=value):
                self.record.write_text(json.dumps({**original, field: value}))
                with self.assertRaises(ValueError):
                    compiler_environment(self.root, {})
        self.record.write_text(json.dumps({**original, "OTHER": "unexpected"}))
        with self.assertRaises(ValueError):
            compiler_environment(self.root, {})

    def test_dangling_artifact_mapping_is_rejected(self):
        (self.root / "_build/default").unlink()
        (self.root / "_build/default").symlink_to(self.root / "absent/default")
        with self.assertRaisesRegex(ValueError, "unavailable"):
            compiler_environment(self.root, {})

    def test_private_build_cannot_leave_the_workspace(self):
        (self.root / "_build/default").unlink()
        with tempfile.TemporaryDirectory() as outside:
            target = Path(outside) / "default"
            target.mkdir()
            (self.root / "_build/default").symlink_to(target)
            with self.assertRaisesRegex(ValueError, "leaves its workspace"):
                compiler_environment(self.root, {})

    def test_two_private_builds_keep_separate_records(self):
        self.write_record()
        first = self.record.read_bytes()
        second = self.root / "_build/agents/second"
        tools = second / "default/tools"
        tools.mkdir(parents=True)
        (self.root / "_build/default").unlink()
        (self.root / "_build/default").symlink_to(second / "default")
        record_dune_environment(tools, {"OCAMLPATH": "/second/lib"})
        self.assertEqual(compiler_environment(self.root, {})["OCAMLPATH"], "/second/lib")
        self.assertEqual(self.record.read_bytes(), first)

    def test_independent_dune_build_preserves_active_fallback_mapping(self):
        self.write_record()
        first = self.record.read_bytes()
        second = self.root / "_build/agents/gate"
        tools = second / "default/tools"
        tools.mkdir(parents=True)
        library = second / "install/default/lib"
        library.mkdir(parents=True)
        recorded = record_dune_environment(tools, {"OCAMLPATH": str(library)})
        self.assertEqual(recorded, second / RECORD_NAME)
        record = json.loads(recorded.read_text())
        self.assertEqual(record["private_build"], str(second))
        self.assertEqual(record["OCAMLPATH"], str(library))
        self.assertEqual((self.root / "_build/default").resolve(), self.build / "default")
        self.assertEqual(self.record.read_bytes(), first)
        self.assertEqual(compiler_environment(self.root, {"OCAMLPATH": str(library)})["OCAMLPATH"],
                         str(self.library))

    def test_missing_dune_value_and_relative_paths_are_rejected(self):
        for environment in ({}, {"OCAMLPATH": "relative/lib"}):
            with self.subTest(environment=environment):
                with self.assertRaises(ValueError):
                    record_dune_environment(self.tools, environment)
        self.assertFalse(self.record.exists())

    def test_path_separators_and_multiple_entries_remain_exact(self):
        value = f"{self.library}:/ordinary/lib:"
        record_dune_environment(self.tools, {"OCAMLPATH": value})
        self.assertEqual(compiler_environment(self.root, {})["OCAMLPATH"], value)

    def test_source_wrapper_without_private_recipe_does_not_record(self):
        tools = self.root / "tools"
        tools.mkdir()
        self.assertIsNone(record_dune_environment(tools, {}))
        self.assertFalse(self.record.exists())

    def test_guard_wait_failure_preserves_status_without_starting_scope(self):
        guard = self.root / "guard"
        guard.write_text("#!/bin/sh\n[ \"$1\" = wait ] && exit 75\nexit 99\n")
        guard.chmod(0o755)
        result = subprocess.run(["python3", str(TOOLS / "coqc_findlib.py"), "guarded",
                                 "--guard", str(guard), "--", "/absent/coqc", "Probe.v"],
                                cwd=self.root, env=fixture_environment(),
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 75)
        self.assertEqual(result.stderr, "")

    def test_wrappers_preserve_arguments_and_the_normal_guard(self):
        (self.tools / "guard-bin").mkdir()
        shutil.copy2(TOOLS / "dune_coqc_guarded.sh", self.tools / "guard-bin/coqc")
        shutil.copy2(TOOLS / "coqc_findlib.py", self.tools / "coqc_findlib.py")
        source_tools = self.root / "tools"
        source_tools.mkdir()
        for name in ("rocq_coqc_guarded.sh", "coqc_findlib.py"):
            shutil.copy2(TOOLS / name, source_tools / name)
        log = self.root / "guard.jsonl"
        guard = self.tools / "resource_guard.sh"
        guard.write_text("#!/usr/bin/env python3\nimport json,os,sys\n"
                         "with open(os.environ['TEST_RECORD'], 'a') as stream:\n"
                         " stream.write(json.dumps({'args':sys.argv[1:], 'OCAMLPATH':os.environ.get('OCAMLPATH')})+'\\n')\n")
        guard.chmod(0o755)
        compiler = self.root / "switch/bin/coqc"
        compiler.parent.mkdir(parents=True)
        compiler.write_text("#!/bin/sh\nexit 99\n")
        compiler.chmod(0o755)
        environment = fixture_environment(OPAM_SWITCH_PREFIX=str(compiler.parent.parent),
                                          OCAMLPATH=str(self.library), TEST_RECORD=str(log))
        arguments = ["-Q", "a space", "", "Probe.v"]
        subprocess.run([str(self.tools / "guard-bin/coqc"), *arguments],
                       cwd=self.build / "default", env=environment, check=True)
        fallback_environment = {**environment, "OCAMLPATH": "/another/private/lib",
                                "ZESU_RESOURCE_GUARD": str(guard)}
        subprocess.run([str(source_tools / "rocq_coqc_guarded.sh"), *arguments],
                       cwd=self.root, env=fallback_environment, check=True)
        records = [json.loads(line) for line in log.read_text().splitlines()]
        self.assertEqual(records[0]["args"], ["scope", "dune-coqc", "--", str(compiler), *arguments])
        self.assertEqual(records[1]["args"], ["wait"])
        self.assertEqual(records[2]["args"], ["scope", "rocq-mcp-coqc", "--", str(compiler), *arguments])
        self.assertTrue(all(record["OCAMLPATH"] == str(self.library) for record in records))
        # The fake guard records each route and never executes a Rocq compiler.


if __name__ == "__main__":
    unittest.main()
