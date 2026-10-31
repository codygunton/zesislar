"""Import the actual staged compiler closure with no parent tools path."""
import json
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import scratch


class StagedMemoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.tools = self.root / 'owned/tools'
        self.harness = Path(scratch.__file__).resolve().parent
        for relative, source in json.loads((self.harness / 'TOOL-LAYOUT.json').read_text()).items():
            target = self.tools / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.harness / source, target)

    def run_import(self, *, compiler=False, ambient=None):
        code = 'import sys;sys.path.insert(0,sys.argv[1]);'
        code += 'import entry_chain_compiler;' if compiler else ''
        code += 'import module_memory;print(module_memory.compiler_pids.__globals__["__file__"])'
        environment = dict(os.environ, PYTHONPATH=str(ambient or ''), PYTHONDONTWRITEBYTECODE='1')
        return subprocess.run([sys.executable, '-B', '-c', code, str(self.tools / 'block')],
                              cwd=self.root, env=environment, capture_output=True, text=True)

    def compiler_fixture(self, *, seed=False):
        """Test data only. This runtime grants no admission or proof authority."""
        workspace = self.tools.parent
        source = workspace / 'Control.v'
        source.write_text('Lemma staged_control : True. Proof. exact I. Qed.\n')
        output = self.root / 'job'
        output.mkdir()
        def binding(path):
            return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        runtime = {'bindings': [binding(path) for path in self.tools.rglob('*') if path.is_file()]
                   + [binding(source)], 'expected_mcp_flags': [], 'physical_flags': [],
                   'job_output': str(output), 'phase': 'prerequisites',
                   'prepared_workspace': str(workspace), 'module_files': {'Control': 'Control.v'}}
        if seed:
            inventory = self.root / 'FILES.jsonl'
            inventory.write_text(json.dumps({'relative': 'Control.v', 'sha256': binding(source)['sha256']}) + '\n')
            seed_runtime = self.root / 'SEED-RUNTIME.json'
            seed_runtime.write_text('{}\n')
            descriptor = self.root / 'SEED.json'
            descriptor.write_text(json.dumps({'schema': 'scratch.shared-seed-bindings.v1',
                'seed_runtime': binding(seed_runtime), 'inventory': binding(inventory),
                'prepared_workspace': str(workspace), 'symlinks': []}))
            runtime['seed_binding_reference'] = {'descriptor': binding(descriptor),
                'workspace': str(workspace), 'deltas': [], 'removed': []}
        path = self.root / 'RUNTIME.json'
        path.write_text(json.dumps(runtime))
        return path, binding(path)['sha256'], source, output

    def run_dispatch(self, fixture):
        path, digest, source, output = fixture
        # Replace only the final exec boundary. Every validation function is real.
        code = '''import json,sys
from pathlib import Path
sys.path.insert(0,sys.argv.pop(1))
import entry_chain_compiler as compiler
def dispatched(executable,argv):
    names=['entry_chain_compiler','entry_chain_resources','proof_bindings','binding_cache','seed_bindings']
    origins={name:sys.modules[name].__file__ for name in names if name in sys.modules}
    print(json.dumps({'executable':executable,'argv':argv,'origins':origins}))
compiler.os.execv=dispatched
compiler.main()
'''
        environment = dict(os.environ, PYTHONPATH='', PYTHONDONTWRITEBYTECODE='1',
            ENTRY_CHAIN_RUNTIME_JSON=str(path), ENTRY_CHAIN_RUNTIME_SHA256=digest,
            ROCQ_WORKSPACE=str(self.tools.parent))
        return subprocess.run([sys.executable, '-B', '-c', code, str(self.tools / 'block'), str(source)],
                              cwd=self.root, env=environment, capture_output=True, text=True)

    def assert_dispatched(self, fixture, *, seed=False):
        result = self.run_dispatch(fixture)
        self.assertEqual(result.returncode, 0, result.stderr)
        record = json.loads(result.stdout)
        expected = {'entry_chain_compiler', 'entry_chain_resources', 'proof_bindings', 'binding_cache'}
        if seed:
            expected.add('seed_bindings')
        self.assertEqual(set(record['origins']), expected)
        for name, origin in record['origins'].items():
            self.assertEqual(Path(origin), self.tools / 'block' / (name + '.py'))
        self.assertIn(str(self.tools / 'coqc_findlib.py'), record['argv'])
        self.assertIn(str(self.tools / 'block/compile_measure.py'), record['argv'])
        inputs = list(fixture[3].glob('compiler-invocations/*/INPUT.json'))
        self.assertEqual(len(inputs), 1)
        physical = json.loads(inputs[0].read_text())
        self.assertEqual(physical['physical_argv'],
                         ['/home/cody/islaris/_opam/bin/coqc', str(fixture[2])])
        self.assertEqual(physical['incoming_argv'], [str(fixture[2])])

    def test_actual_dispatch_executes_lazy_binding_validation(self):
        self.assert_dispatched(self.compiler_fixture())

    def test_actual_dispatch_executes_owned_seed_validation(self):
        fixture = self.compiler_fixture(seed=True)
        self.assert_dispatched(fixture, seed=True)
        report = json.loads((fixture[3] / 'VALIDATION-WORK.jsonl').read_text())
        self.assertEqual(report['shared_seed_files_checked'], 1)
        self.assertTrue(report['source_bindings_checked'])

    def test_changed_proof_input_refuses_before_dispatch(self):
        fixture = self.compiler_fixture()
        fixture[2].write_text('changed\n')
        result = self.run_dispatch(fixture)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('A chain input changed:', result.stderr)
        self.assertFalse((fixture[3] / 'compiler-invocations').exists())

    def test_changed_seed_input_refuses_before_dispatch(self):
        fixture = self.compiler_fixture(seed=True)
        fixture[2].write_text('changed\n')
        result = self.run_dispatch(fixture)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('An owned seed input changed:', result.stderr)
        self.assertFalse((fixture[3] / 'compiler-invocations').exists())

    def test_missing_cache_refuses_before_dispatch(self):
        fixture = self.compiler_fixture()
        (self.tools / 'block/binding_cache.py').unlink()
        result = self.run_dispatch(fixture)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("No module named 'binding_cache'", result.stderr)
        self.assertFalse((fixture[3] / 'compiler-invocations').exists())

    def test_missing_seed_validator_refuses_before_dispatch(self):
        fixture = self.compiler_fixture(seed=True)
        (self.tools / 'block/seed_bindings.py').unlink()
        result = self.run_dispatch(fixture)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("No module named 'seed_bindings'", result.stderr)
        self.assertFalse((fixture[3] / 'compiler-invocations').exists())

    def test_actual_compiler_import_resolves_owned_dependency(self):
        result = self.run_import(compiler=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(Path(result.stdout.strip()), self.tools / 'det/coqc_slots.py')

    def test_ambient_det_cannot_replace_owned_dependency(self):
        ambient = self.root / 'ambient'
        package = ambient / 'det'
        package.mkdir(parents=True)
        (package / '__init__.py').write_text('raise RuntimeError("ambient det loaded")\n')
        result = self.run_import(ambient=ambient)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(Path(result.stdout.strip()), self.tools / 'det/coqc_slots.py')

    def test_missing_owned_dependency_refuses_ambient_fallback(self):
        (self.tools / 'det/coqc_slots.py').unlink()
        result = self.run_import()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('lacks its owned det dependency', result.stderr)

    def test_dependency_symlink_outside_owned_tools_refuses(self):
        slots = self.tools / 'det/coqc_slots.py'
        foreign = self.root / 'foreign.py'
        shutil.copyfile(slots, foreign)
        slots.unlink()
        slots.symlink_to(foreign)
        result = self.run_import()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('lacks its owned det dependency', result.stderr)


if __name__ == '__main__':
    unittest.main()
