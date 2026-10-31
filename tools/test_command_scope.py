"""Check whole-command containment without starting systemd or proof tools."""
import ast
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'block/harness'))
import command_scope


class CommandScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.proc = self.root / 'cgroup'
        self.cgroups = self.root / 'sys'
        self.parent = self.cgroups / 'user.slice/zesuworkloads.slice'
        self.parent.mkdir(parents=True)
        (self.parent / 'memory.max').write_text(str(command_scope.PARENT_BYTES))
        (self.parent / 'memory.swap.max').write_text('0')

    def contained(self):
        return command_scope.contained(proc=self.proc, cgroups=self.cgroups)

    def test_existing_parent_and_nested_aggregate_are_accepted(self):
        for group in ['/user.slice/zesuworkloads.slice/job.scope',
                      '/user.slice/zesuworkloads.slice/zesuworkloads-aggregate1.slice/job.scope']:
            self.proc.write_text('0::' + group + '\n')
            self.assertTrue(self.contained())
            calls = []
            command_scope.enter('/repo/tools/block/harness/scratch.py', ['--prepare-only'],
                                check=self.contained, run=lambda *a, **k: calls.append(a),
                                execute=lambda *a: calls.append(a))
            self.assertEqual(calls, [])

    def test_environment_flag_cannot_replace_actual_membership(self):
        self.proc.write_text('0::/user.slice/ordinary.scope\n')
        with patch.dict('os.environ', {'ZESU_IN_GATE': '1', 'ZESU_IN_SHARED_SCOPE': '1'}):
            self.assertFalse(self.contained())

    def test_changed_parent_backstop_refuses(self):
        self.proc.write_text('0::/user.slice/zesuworkloads.slice/job.scope\n')
        for name, invalid in [('memory.max', 'max'), ('memory.swap.max', '1')]:
            path = self.parent / name
            original = path.read_text()
            path.write_text(invalid)
            with self.assertRaisesRegex(ValueError, 'backstop'): self.contained()
            path.write_text(original)

    def test_setup_precedes_exact_argv_exec(self):
        events = []
        arguments = ['--prepare-only', 'literal $(false)', '$secret', '; false']
        def run(argv, **kwargs): events.append(('setup', argv, kwargs))
        def execute(executable, argv, environment):
            events.append(('exec', executable, argv, environment))
        with self.assertRaisesRegex(RuntimeError, 'returned'):
            command_scope.enter('/repo/tools/block/harness/scratch.py', arguments,
                                check=lambda: False, run=run, execute=execute)
        self.assertEqual(events[0], ('setup', ['/repo/tools/resource_guard.sh', 'parent-setup'], {'check': True}))
        command = events[1][2]
        self.assertIn('--slice=zesuworkloads.slice', command)
        self.assertIn('MemorySwapMax=0', command)
        self.assertEqual(command[-len(arguments):], arguments)
        self.assertIn('parent-exec', command)
        self.assertFalse(any(item.startswith('MemoryMax=') for item in command))

    def test_parent_setup_failure_stops_exec(self):
        calls = []
        def fail(argv, **kwargs): raise subprocess.CalledProcessError(2, argv)
        with self.assertRaises(subprocess.CalledProcessError):
            command_scope.enter('/repo/tools/block/harness/scratch.py', [], check=lambda: False,
                                run=fail, execute=lambda *args: calls.append(args))
        self.assertEqual(calls, [])

    def test_imported_operations_refuse_outside_the_parent(self):
        with patch.object(command_scope, 'contained', return_value=False):
            with self.assertRaisesRegex(ValueError, 'must run inside'): command_scope.require()
        with patch.object(command_scope, 'contained', return_value=True):
            command_scope.require()

    def test_each_shared_operation_checks_containment_first(self):
        tree = ast.parse((Path(command_scope.__file__).parent / 'scratch.py').read_text())
        names = {'prepare', 'execute', 'execute_retained', 'refresh_memory'}
        found = set()
        for node in tree.body:
            if isinstance(node, ast.FunctionDef) and node.name in names:
                found.add(node.name)
                self.assertIsInstance(node.body[0], ast.ImportFrom)
                self.assertEqual(node.body[0].module, 'command_scope')
                self.assertIsInstance(node.body[1], ast.Expr)
                self.assertEqual(node.body[1].value.func.id, 'require')
        self.assertEqual(found, names)

    def test_scope_entry_precedes_shared_imports(self):
        tree = ast.parse((Path(command_scope.__file__).parent / 'scratch.py').read_text())
        guard = next(i for i, node in enumerate(tree.body)
                     if isinstance(node, ast.If) and any(isinstance(call, ast.Call)
                     and isinstance(call.func, ast.Name) and call.func.id == 'enter'
                     for call in ast.walk(node)))
        imports = [i for i, node in enumerate(tree.body) if isinstance(node, (ast.Import, ast.ImportFrom))
                   and (getattr(node, 'module', '') == 'entry_chain'
                        or any(alias.name == 'clone_copy' for alias in getattr(node, 'names', [])))]
        self.assertTrue(imports)
        self.assertTrue(all(guard < index for index in imports))


if __name__ == '__main__': unittest.main()
