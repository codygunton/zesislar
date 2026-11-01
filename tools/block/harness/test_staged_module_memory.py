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

    def test_missing_admission_dependency_cannot_borrow_ambient_module(self):
        ambient=self.root/'ambient';ambient.mkdir()
        (ambient/'admission_memory.py').write_text('raise RuntimeError("AMBIENT MODULE USED")')
        (self.tools/'block/admission_memory.py').unlink()
        result=self.run_import(ambient=ambient)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('owned admission dependency',result.stderr)
        self.assertNotIn('AMBIENT MODULE USED',result.stderr)

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

    def measured_snapshot_fixture(self, *, multiple=False, emit_sidecar=True):
        """Use a fake executable at the physical boundary. Run no Rocq process."""
        import compiler_snapshot as snapshots
        from entry_chain import binding, save
        path, _, source, output = self.compiler_fixture()
        source.write_text('Nonproof staged input fixture.\n')
        compiler = self.root / 'switch/bin/coqc'
        compiler.parent.mkdir(parents=True)
        compiler.write_text('#!/usr/bin/python3\nimport json,os,pathlib,sys\n'
            'print(json.dumps({"key_present":"ENTRY_CHAIN_COMPILER_SNAPSHOT_OUTPUT_KEY" in os.environ}))\n'
            'pathlib.Path(sys.argv[-1]).with_suffix(".vo").write_text("nonproof fake output")\n'
            + ('sidecar=pathlib.Path(sys.argv[-1]).with_suffix(".vos")\n'
               'if not sidecar.exists():sidecar.write_bytes(b"")\n' if emit_sidecar else ''))
        compiler.chmod(0o755)
        runtime = json.loads(path.read_text())
        runtime['physical_compiler']=binding(compiler)
        runtime['bindings'] = [binding(row['path']) for row in runtime['bindings']] + [binding(compiler)]
        if multiple:
            artifacts=self.tools.parent/'artifacts/default';artifacts.mkdir(parents=True)
            moved=artifacts/source.name;shutil.copyfile(source,moved);source=moved
            runtime['module_files']['Control']=str(source.relative_to(self.tools.parent))
            runtime['bindings'].append(binding(source))
            (self.tools.parent/'default').symlink_to('artifacts/default',target_is_directory=True)
            second=artifacts/'Second.v';second.write_text('Second nonproof source fixture.\n')
            runtime['module_files']['Second']=str(second.relative_to(self.tools.parent))
            runtime['bindings'].append(binding(second))
            donor=self.root/'donor';donor.mkdir()
            self.donor_rows=[]
            for original in [source,second]:
                retained=donor/original.name;retained.write_bytes(original.read_bytes())
                obj=retained.with_suffix('.vo');obj.write_text('nonproof fake output')
                self.donor_rows.extend([binding(retained),binding(obj)])
                original.with_suffix('.vo').write_bytes(obj.read_bytes())
            runtime['bindings'].extend(self.donor_rows)
            runtime['ordered_modules']=['Control','Second']
            runtime['physical_flags']=['-Q',str(self.tools.parent/'default'),'Fixture']
            runtime['declared_outputs']=snapshots.declared_outputs(runtime['module_files'],
                runtime['ordered_modules'],self.tools.parent,runtime['bindings'],donor=donor)
        snapshots.externalize(runtime, self.root / 'BINDINGS.json')
        save(path, runtime)
        runtime_reference = binding(path)
        runtime.update(runtime_path=str(path), runtime_sha256=runtime_reference['sha256'])
        reference = snapshots.publish(runtime,
            lambda: __import__('proof_bindings').check_proof_bindings(runtime, force_full=True),
            output / 'SNAPSHOT.json',compiler=compiler,environment={})
        ledger = snapshots.OutputReceipts(snapshots.read(reference, runtime_reference), reference)
        self.output_receipts=ledger
        invocation = output / 'compiler-invocations/invocation'
        invocation.mkdir(parents=True)
        save(invocation / 'INPUT.json', {'owned_workspace': str(self.tools.parent),
            'source': binding(source), 'compiler': binding(compiler),
            'physical_argv': [str(compiler), *runtime['physical_flags'], str(source)],
            'validation': {'runtime': runtime_reference, 'snapshot': reference}})
        environment = dict(os.environ, PYTHONPATH='', PYTHONDONTWRITEBYTECODE='1',
            ENTRY_CHAIN_COMPILER_SNAPSHOT_OUTPUT_KEY=ledger.key)
        return invocation, environment, source, runtime

    def measure_dispatch(self, invocation, environment):
        return subprocess.run([sys.executable, '-B', str(self.tools / 'block/compile_measure.py'), str(invocation)],
            cwd=self.tools.parent, env=environment, capture_output=True, text=True)

    def test_staged_snapshot_reaches_physical_boundary_without_leaking_key(self):
        invocation, environment, source, runtime = self.measured_snapshot_fixture()
        result = self.measure_dispatch(invocation, environment)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), {'key_present': False})
        self.assertTrue(source.with_suffix('.vo').is_file())
        report = json.loads((invocation / 'PHYSICAL-VALIDATION.json').read_text())
        self.assertGreater(report['retained_identities_checked'], 60)
        self.assertEqual(json.loads((invocation / 'PHYSICAL-RESULT.json').read_text())['returncode'], 0)
        self.assertNotIn(environment['ENTRY_CHAIN_COMPILER_SNAPSHOT_OUTPUT_KEY'],
                         ''.join(path.read_text() for path in invocation.iterdir() if path.is_file()))

    def test_staged_snapshot_changed_source_refuses_before_physical_boundary(self):
        invocation, environment, source, runtime = self.measured_snapshot_fixture()
        source.write_text('changed source')
        result = self.measure_dispatch(invocation, environment)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('compiler input identity changed', result.stderr)
        self.assertFalse(source.with_suffix('.vo').exists())
        self.assertFalse((invocation / 'PHYSICAL-RESULT.json').exists())

    def test_unclassified_generated_source_cannot_change_during_admission(self):
        from entry_chain import binding,save
        invocation,environment,source,runtime=self.measured_snapshot_fixture()
        generated=self.tools.parent/'Generated.v'
        generated.write_text('unclassified generated test input')
        record=json.loads((invocation/'INPUT.json').read_text())
        record['source']=binding(generated)
        record['physical_argv'][-1]=str(generated)
        save(invocation/'INPUT.json',record)
        generated.write_text('changed while admission waited')
        result=self.measure_dispatch(invocation,environment)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('recorded physical source changed during admission',result.stderr)
        self.assertFalse(generated.with_suffix('.vo').exists())
        self.assertFalse((invocation/'PHYSICAL-RESULT.json').exists())

    def test_multiple_compiles_and_identical_source_recompile_preserve_donor(self):
        from entry_chain import binding,save
        from proof_bindings import check_proof_bindings
        import compiler_snapshot as snapshots
        invocation,environment,source,runtime=self.measured_snapshot_fixture(multiple=True)
        template=json.loads((invocation/'INPUT.json').read_text())
        snapshot=snapshots.read(template['validation']['snapshot'],template['validation']['runtime'])
        objects={str((self.tools.parent/name).with_suffix('.vo')) for name in runtime['module_files'].values()}
        self.assertTrue(objects.isdisjoint({row['path'] for row in snapshot['rows']}))
        self.assertTrue(all(not Path(path).exists() for path in objects))
        for number,name in enumerate(['Control.v','Second.v','Control.v']):
            selected=self.tools.parent/runtime['module_files'][Path(name).stem]
            current=invocation if number==0 else invocation.with_name('invocation'+str(number))
            current.mkdir(exist_ok=True)
            record=dict(template,source=binding(selected),
                physical_argv=[template['physical_argv'][0],*runtime['physical_flags'],str(selected)])
            save(current/'INPUT.json',record)
            result=self.measure_dispatch(current,environment)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(json.loads(result.stdout),{'key_present':False})
            check_proof_bindings(runtime,force_full=True)
            self.output_receipts.accept(selected,selected.with_suffix('.vo'),
                record['compiler']['path'],runtime['physical_flags'],{'success':True,'returncode':0},
                physical_result=binding(current/'PHYSICAL-RESULT.json'))
            self.assertEqual([binding(row['path']) for row in self.donor_rows],self.donor_rows)
            physical=json.loads((current/'PHYSICAL-RESULT.json').read_text())
            inputs=json.loads((current/'INPUT.json').read_text())
            expected='retained_authenticated_output' if number==2 else 'absent'
            self.assertEqual(inputs['sidecar_prestate']['state'],expected)
            if number==2:
                self.assertEqual(inputs['sidecar_prestate']['prior_receipt'],self.output_receipts.rows[0])
                self.assertEqual(physical['compiler_outputs']['sidecar_status'],'retained_authenticated_output')
        self.assertEqual(len(self.output_receipts.rows),3)
        final=snapshots.validate_compiler(runtime,template['validation']['runtime'],
            template['validation']['snapshot'],binding(source),template['physical_argv'][0],
            output_key=self.output_receipts.key)
        self.assertEqual(len(final['accepted_dependency_objects']),3)

    def test_missing_compiler_sidecar_keeps_actual_physical_result(self):
        invocation,environment,source,runtime=self.measured_snapshot_fixture(emit_sidecar=False)
        result=self.measure_dispatch(invocation,environment)
        self.assertNotEqual(result.returncode,0)
        physical=json.loads((invocation/'PHYSICAL-RESULT.json').read_text())
        self.assertEqual(physical['returncode'],0)
        self.assertFalse(physical['output_validation']['success'])
        self.assertTrue(source.with_suffix('.vo').is_file())
        self.assertFalse(source.with_suffix('.vos').exists())
        self.assertEqual(self.output_receipts.rows,[])

    def test_independently_introduced_empty_sidecar_refuses_before_coqc(self):
        invocation,environment,source,runtime=self.measured_snapshot_fixture(multiple=True)
        source.with_suffix('.vos').write_bytes(b'')
        result=self.measure_dispatch(invocation,environment)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('lacks a validated receipt',result.stderr)
        self.assertFalse((invocation/'PHYSICAL-RESULT.json').exists())
        self.assertFalse(source.with_suffix('.vo').exists())

    def retained_sidecar_fixture(self):
        from entry_chain import binding,save
        invocation,environment,source,runtime=self.measured_snapshot_fixture(multiple=True)
        result=self.measure_dispatch(invocation,environment)
        self.assertEqual(result.returncode,0,result.stderr)
        original=json.loads((invocation/'INPUT.json').read_text())
        self.output_receipts.accept(source,source.with_suffix('.vo'),original['compiler']['path'],
            runtime['physical_flags'],{'success':True},physical_result=binding(invocation/'PHYSICAL-RESULT.json'))
        next_invocation=invocation.with_name('second');next_invocation.mkdir()
        save(next_invocation/'INPUT.json',original)
        return next_invocation,environment,source,runtime

    def test_retained_sidecar_mutation_refuses_before_recompile(self):
        invocation,environment,source,runtime=self.retained_sidecar_fixture()
        source.with_suffix('.vos').write_bytes(b'changed sidecar')
        result=self.measure_dispatch(invocation,environment)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('accepted compilation input changed',result.stderr)
        self.assertFalse((invocation/'PHYSICAL-RESULT.json').exists())

    def test_retained_sidecar_same_byte_replacement_refuses_before_recompile(self):
        invocation,environment,source,runtime=self.retained_sidecar_fixture()
        sidecar=source.with_suffix('.vos');replacement=sidecar.with_suffix('.replacement')
        replacement.write_bytes(sidecar.read_bytes());replacement.replace(sidecar)
        result=self.measure_dispatch(invocation,environment)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('object identity changed',result.stderr)
        self.assertFalse((invocation/'PHYSICAL-RESULT.json').exists())


if __name__ == '__main__':
    unittest.main()
