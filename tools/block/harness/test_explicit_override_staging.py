"""Exercise the actual override loop with mandatory reflinks."""
import ast
import hashlib
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest

import scratch
from entry_chain_stage import invalidation


HERE = Path(__file__).resolve().parent
TEMP=Path('/home/cody/.cache/zesislar/shared-harness-tests')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ExplicitOverrideTests(unittest.TestCase):
    def stage(self, root, replacement=None, bad_hash=False):
        module = 'Test.Module'
        protected = root / 'seed/Module.v'
        incoming = root / 'private/Module.v'
        target = root / 'workspace/Test/Module.v'
        for path in [protected, incoming, target]:
            path.parent.mkdir(parents=True, exist_ok=True)
        protected.write_bytes(b'Require Import isla.isla.\n')
        protected.chmod(0o444)
        scratch.clone_copy.copy2(protected, incoming)
        incoming.chmod(0o644)
        if replacement is not None:
            incoming.write_bytes(replacement)
        scratch.clone_copy.copy2(protected, target)
        row = {'module': module, 'path': str(incoming),
               'sha256': '0' * 64 if bad_hash else digest(incoming)}
        tree = ast.parse((HERE / 'scratch.py').read_text())
        prepare = next(node for node in tree.body
                       if isinstance(node, ast.FunctionDef) and node.name == 'prepare')
        loop = next(node for node in prepare.body
                    if isinstance(node, ast.For) and isinstance(node.target, ast.Name)
                    and node.target.id == 'override')
        def resolution(name, *, origin):
            self.assertEqual((name, origin), ('isla.isla', incoming))
            return {'canonical': 'isla.isla'}
        scope = dict(vars(scratch), overrides=[row], seen=set(),
                     modules={module: 'Test/Module.v'}, workspace=root / 'workspace',
                     edges=[{'from': module, 'to': 'isla.isla'}], changed=[],
                     installed=SimpleNamespace(register_source=lambda *args: None,
                         resolution=resolution))
        code = compile(ast.fix_missing_locations(ast.Module(body=[loop], type_ignores=[])),
                       '<actual-override-loop>', 'exec')
        if bad_hash:
            with self.assertRaises(ValueError):
                exec(code, scope)
        else:
            exec(code, scope)
        return protected, incoming, target, scope

    def test_identical_override_replaces_readonly_clone_and_keeps_seed(self):
        with tempfile.TemporaryDirectory(dir=TEMP) as directory:
            seed, incoming, target, scope = self.stage(Path(directory))
            self.assertEqual(scope['changed'], [])
            self.assertEqual(seed.read_bytes(), incoming.read_bytes())
            self.assertEqual(target.read_bytes(), incoming.read_bytes())
            self.assertEqual(seed.stat().st_mode & 0o777, 0o444)
            self.assertEqual(incoming.stat().st_mode & 0o777, 0o644)
            self.assertEqual(target.stat().st_mode & 0o777, 0o644)
            self.assertEqual(len({path.stat().st_ino for path in [seed, incoming, target]}), 3)
            target.write_text('owned target changed\n')
            self.assertEqual(seed.read_bytes(), b'Require Import isla.isla.\n')
            self.assertEqual(incoming.read_bytes(), seed.read_bytes())
            self.assertEqual(seed.stat().st_mode & 0o777, 0o444)

    def test_changed_source_keeps_dependency_invalidation(self):
        with tempfile.TemporaryDirectory(dir=TEMP) as directory:
            seed, incoming, target, scope = self.stage(
                Path(directory), b'Require Import isla.isla.\nDefinition changed := 1.\n')
            self.assertEqual(scope['changed'], ['Test.Module'])
            self.assertEqual(target.read_bytes(), incoming.read_bytes())
            edges = scope['edges'] + [{'from': 'Test.Child', 'to': 'Test.Module'}]
            plan = invalidation(edges, scope['changed'], ['Test.Child'])
            self.assertEqual(set(plan['invalidated_modules']), {'Test.Module', 'Test.Child'})
            self.assertEqual(plan['ordered_required'], ['Test.Module', 'Test.Child'])
            self.assertEqual(seed.read_bytes(), b'Require Import isla.isla.\n')
            self.assertEqual(seed.stat().st_mode & 0o777, 0o444)

    def test_byte_only_change_still_invalidates(self):
        with tempfile.TemporaryDirectory(dir=TEMP) as directory:
            _, incoming, target, scope = self.stage(Path(directory), b'Require Import isla.isla.\r\n')
            self.assertEqual(scope['changed'], ['Test.Module'])
            self.assertEqual(target.read_bytes(), incoming.read_bytes())

    def test_wrong_source_hash_refuses_before_staging(self):
        with tempfile.TemporaryDirectory(dir=TEMP) as directory:
            seed, _, target, _ = self.stage(Path(directory), bad_hash=True)
            self.assertEqual(target.read_bytes(), seed.read_bytes())
            self.assertEqual(target.stat().st_mode & 0o777, 0o444)


if __name__ == '__main__':
    unittest.main()
