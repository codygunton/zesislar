"""Check compiler recipes after a cached build."""

import hashlib
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from coqc_recipe import compiler_recipe, remember_recipe, snapshot_recipe, read_snapshot


def csexp(value):
    if isinstance(value, list):
        return b"(" + b"".join(map(csexp, value)) + b")"
    atom = value.encode()
    return str(len(atom)).encode() + b":" + atom


class CompilerRecipeTests(unittest.TestCase):
    def test_preserves_recipe_after_cached_build(self):
        event = ["process", "start", "1", ["prog", "/switch/bin/coqc"],
                 ["process_args", ["-q", "-Q", "ZesuSsz", "ZesuSsz", "Test.v"]],
                 ["dir", "/private/default"]]
        with tempfile.TemporaryDirectory() as directory:
            build_dir = Path(directory)
            trace = build_dir / "trace.csexp"
            trace.write_bytes(csexp(event))
            expected = remember_recipe(build_dir)
            trace.write_bytes(csexp(["build", "cached"]))
            self.assertEqual(remember_recipe(build_dir), expected)
            self.assertEqual(expected["command"][-1], "Test.v")
            self.assertEqual(expected["working_dir"], "/private/default")

    def test_project_recipe_survives_later_trace_compilation(self):
        project = ["process", "start", "1", ["prog", "/switch/bin/coqc"],
                   ["process_args", ["-R", "ZesuSsz", "ZesuSsz", "ZesuSsz/Proof.v"]]]
        trace = ["process", "start", "2", ["prog", "/switch/bin/coqc"],
                 ["process_args", ["-Q", "ZesuSsz", "ZesuSsz", "-R", "generated", "IslaTraces", "generated/Trace.v"]]]
        expected = compiler_recipe(csexp(project))
        self.assertEqual(compiler_recipe(csexp(project) + csexp(trace)), expected)
        with tempfile.TemporaryDirectory() as directory:
            build_dir = Path(directory)
            (build_dir / "trace.csexp").write_bytes(csexp(project))
            cached = remember_recipe(build_dir)
            (build_dir / "trace.csexp").write_bytes(csexp(trace))
            self.assertEqual(remember_recipe(build_dir), cached)

    def test_rejects_noncompiler_process(self):
        event = ["process", "start", "1", ["prog", "/bin/echo"],
                 ["process_args", ["coqc", "Test.v"]]]
        self.assertIsNone(compiler_recipe(csexp(event)))

    def test_missing_recipe(self):
        with tempfile.TemporaryDirectory() as directory:
            self.assertIsNone(remember_recipe(Path(directory)))

    def test_incomplete_event(self):
        event = ["process", "start", "1", ["prog", "/switch/bin/coqc"],
                 ["process_args", ["-q", "Test.v"]]]
        data = csexp(event)
        self.assertEqual(compiler_recipe(data + b"(7:partial"), compiler_recipe(data))
        self.assertIsNone(compiler_recipe(data[:-1]))


class SnapshotTests(unittest.TestCase):
    def event(self, source='ZesuSsz/First.v', flags=('-q',)):
        return csexp(['process', 'start', '1', ['prog', '/switch/bin/coqc'],
            ['process_args', [*flags, source]], ['dir', '/private/default']])

    def test_later_source_or_flags_do_not_change_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            trace = build / 'trace.csexp'
            trace.write_bytes(self.event())
            snapshot = build / 'AttemptRecipe.json'
            digest = snapshot_recipe(build, snapshot)
            initial = read_snapshot(snapshot, digest)
            for flags in [('-q',), ('-q', '-Q', 'Other', 'Other')]:
                trace.write_bytes(self.event('ZesuSsz/Later.v', flags))
                self.assertNotEqual(remember_recipe(build), initial)
                self.assertEqual(read_snapshot(snapshot, digest), initial)

    def test_changed_snapshot_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            (build / 'trace.csexp').write_bytes(self.event())
            snapshot = build / 'AttemptRecipe.json'
            digest = snapshot_recipe(build, snapshot)
            snapshot.write_text('{}')
            with self.assertRaisesRegex(ValueError, 'snapshot changed'):
                read_snapshot(snapshot, digest)

    def test_existing_snapshot_is_not_replaced(self):
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            snapshot = build / 'AttemptRecipe.json'
            snapshot.write_text('original')
            with self.assertRaisesRegex(ValueError, 'must be reused'):
                snapshot_recipe(build, snapshot)
            self.assertEqual(snapshot.read_text(), 'original')

    def test_missing_recipe_and_snapshot_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            with self.assertRaisesRegex(ValueError, 'unavailable'):
                snapshot_recipe(build, build / 'AttemptRecipe.json')
            with self.assertRaises(FileNotFoundError):
                read_snapshot(build / 'Missing.json', '0' * 64)


class ScratchSnapshotTests(unittest.TestCase):
    def run_scratch(self, directory, *, tampered=False, partial=False):
        root = Path(directory)
        source = root / 'Proof.v'
        source.write_text('Lemma fixture : True. Proof. exact I. Qed.\n')
        compiler = root / 'compiler'
        compiler.write_text('#!/bin/sh\nprintf "%s\\n" "$@" > "$CAPTURE_ARGUMENTS"\n')
        compiler.chmod(0o755)
        guard = root / 'guard'
        guard.write_text('''#!/bin/sh
case "$1" in
  gate-module-limit) echo 16 ;;
  reserve-coqc) echo fixture ;;
  scope) shift 2; exec "$@" ;;
esac
''')
        guard.chmod(0o755)
        snapshot = root / 'Snapshot.json'
        snapshot.write_text(json.dumps({'command': [str(compiler), '-q',
            '-Q', 'Frozen', 'Frozen', '-o', 'Previous.vo', 'Previous.v'],
            'working_dir': str(root)}) + '\n')
        digest = hashlib.sha256(snapshot.read_bytes()).hexdigest()
        if tampered:
            snapshot.write_text('{}')
        cache = root / 'coqc_recipe.json'
        cache.write_text('cache must remain unchanged')
        arguments = root / 'arguments'
        environment = {**os.environ, 'ZESU_RESOURCE_GUARD': str(guard),
            'ZESU_SCRATCH_RECIPE': str(snapshot),
            'ZESU_SCRATCH_RECIPE_SHA256': digest,
            'CAPTURE_ARGUMENTS': str(arguments)}
        if partial:
            environment.pop('ZESU_SCRATCH_RECIPE_SHA256')
        tool = Path(__file__).resolve().parent / 'coqc_scratch.sh'
        result = subprocess.run([str(tool), str(source), str(root)],
            env=environment, capture_output=True, text=True, timeout=8)
        self.assertEqual(cache.read_text(), 'cache must remain unchanged')
        return result, arguments

    def test_snapshot_works_without_mutable_trace_or_cache_refresh(self):
        with tempfile.TemporaryDirectory() as directory:
            result, arguments = self.run_scratch(directory)
            self.assertEqual(result.returncode, 0, result.stderr)
            flags = arguments.read_text().splitlines()
            self.assertEqual(flags[:4], ['-q', '-Q', 'Frozen', 'Frozen'])
            self.assertNotIn('Previous.vo', flags)
            self.assertNotIn('Previous.v', flags)

    def test_changed_snapshot_stops_before_compiler_entry(self):
        with tempfile.TemporaryDirectory() as directory:
            result, arguments = self.run_scratch(directory, tampered=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('snapshot changed', result.stderr)
            self.assertFalse(arguments.exists())

    def test_partial_snapshot_configuration_stops_before_compiler_entry(self):
        with tempfile.TemporaryDirectory() as directory:
            result, arguments = self.run_scratch(directory, partial=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('requires both path and SHA256', result.stderr)
            self.assertFalse(arguments.exists())
