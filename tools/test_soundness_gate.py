"""Check release-gate selection and refusal without invoking a proof tool."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
import soundness_gate as gate


class SoundnessGateTests(unittest.TestCase):
    def test_checker_wrapper_is_the_accepted_exact_source(self):
        self.assertEqual(hashlib.sha256(gate.WRAPPERS.encode()).hexdigest(),
                         '4a2bad6927e41035c11318c583f2c4d5e92fd1eae60a2dedc0c7ca34f78ecf82')

    def test_wrapper_generator_stays_outside_the_production_shape_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            workspace = Path(directory)
            out = workspace / '_build/agents/test-gate'
            out.mkdir(parents=True)
            build = out / 'build'
            source, artifact = gate.wrapper_paths(workspace, out, build)
            calls = []

            kinds = []

            async def verify(root, sources, pc, report, **kwargs):
                calls.append(list(sources))
                kinds.append((kwargs.get('timeout'), kwargs.get('admission_seconds')))
                artifact.parent.mkdir(parents=True, exist_ok=True)
                artifact.write_bytes(b'fixture object')
                result = {'checks': [{'compile_file': {'output': '\n'.join(['Closed under the global context'] * 4)},
                                     'private_artifact': str(artifact), 'private_artifact_sha256': gate.digest(artifact)}]}
                report.mkdir()
                gate.save(report / 'RESULT.json', result)
                return result

            config = dict(workspace=str(workspace), output=str(out), build=str(build),
                          baseline=str(workspace / 'baseline'), bindings=[])
            with patch.object(gate, 'public_records', return_value=[]), \
                    patch.object(gate.verification, 'verify', side_effect=verify):
                gate.stage(config, 'wrappers')
            self.assertEqual(len(calls), 4)
            self.assertEqual(calls[-1], [source])
            # Each compile gets its limit after guard admission; admission has its own bound.
            self.assertEqual(kinds, [(gate.COMPILE_SECONDS, gate.verification.ADMISSION_WAIT_SECONDS)] * 4)
            self.assertEqual(source.read_text(), gate.WRAPPERS)
            self.assertFalse((workspace / 'ZesuSsz').exists())
            self.assertEqual(artifact, build / 'default/_build/agents/test-gate/scratch/SoundnessGateWrappers.vo')
            self.assertEqual(json.loads((out / 'WRAPPERS.json').read_text())['object'], gate.binding(artifact))

    def test_wrapper_mapping_refuses_an_output_outside_the_workspace(self):
        with self.assertRaises(ValueError):
            gate.wrapper_paths(Path('/workspace'), Path('/other'), Path('/workspace/build'))

    def test_supported_kernel_flags_keep_order_and_omit_compiler_flags(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build = root / 'private'
            recipe = {'working_dir': str(build / 'default'), 'command': [
                'coqc', '-q', '-I', '/plugins', '-boot', '-Q', 'A', 'First',
                '-R', '/library', 'Second', '-coqlib', '/coq', '-w', '-warning', 'Source.v']}
            self.assertEqual(gate.kernel_flags(recipe, root, build), [
                '-boot', '-Q', str(build / 'default/A'), 'First',
                '-R', '/library', 'Second', '-coqlib', '/coq'])

    def test_other_private_build_refuses(self):
        with self.assertRaisesRegex(ValueError, 'another build'):
            gate.kernel_flags({'working_dir': '/other', 'command': ['coqc']}, Path('/root'), Path('/root/build'))

    def test_all_five_negative_candidates_are_present(self):
        sources = gate.control_sources()
        self.assertEqual(set(sources), {'admitted', 'extra_axiom', 'admit_axiom', 'wrong_statement', 'doctored_statement'})
        self.assertIn('Coq.Compat.AdmitAxiom', sources['admit_axiom'])
        self.assertNotIn('Stdlib.', sources['admit_axiom'])
        self.assertIn('True', sources['wrong_statement'])
        self.assertIn('Definition expected := True.', sources['doctored_statement'])

    def test_assumption_refusal_requires_actual_module_m_assumptions(self):
        compiled = {'success': True}
        valid = dict(success=False, verification_method='module_m', reason='axiom_dependency', assumptions=['extra : False'])
        gate.rejected_control('extra_axiom', compiled, valid)
        for changed in ({'assumptions': []}, {'reason': 'compile_error'}, {'verification_method': 'other'}, {'success': True}):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                gate.rejected_control('extra_axiom', compiled, {**valid, **changed})

    def test_missing_import_does_not_count_as_statement_rejection(self):
        for error in ['Cannot find module', 'The command failed', 'Unable to unify True with Other']:
            with self.subTest(error=error), self.assertRaises(ValueError):
                gate.rejected_control('wrong_statement', {'success': True}, {'success': False, 'error': error})
        gate.rejected_control('wrong_statement', {'success': True},
                              {'success': False, 'error': 'Unable to unify True with False'})

    def test_compile_failure_never_counts_as_a_negative_success(self):
        with self.assertRaisesRegex(ValueError, 'compile and then refuse'):
            gate.rejected_control('admitted', {'success': False},
                {'success': False, 'reason': 'axiom_dependency', 'verification_method': 'module_m', 'assumptions': ['bad']})

    def test_trace_staging_rejects_changed_bytes_and_compiled_objects(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / 'build/stock-zisk/build-recipe.json'
            manifest.parent.mkdir(parents=True)
            relative = 'generated/isla-traces/f/a.v'
            target = root / relative
            target.parent.mkdir(parents=True)
            target.write_text('changed')
            manifest.write_text(json.dumps({'project_derived': {relative: {'sha256': '0' * 64}}}))
            with self.assertRaisesRegex(ValueError, 'differs'):
                gate.stage_traces(root, None)
            manifest.write_text(json.dumps({'project_derived': {relative + 'o': {'sha256': '0' * 64}}}))
            with self.assertRaisesRegex(ValueError, 'source inputs'):
                gate.stage_traces(root, None)

    def test_public_selection_keeps_the_four_reviewed_statements(self):
        self.assertEqual(set(gate.PUBLIC), {'decodeItemSelectedCompliance', 'decodeItemSelectedComplianceRegisters',
            'decodeItemSelectedComplianceCompositional', 'decodeItemGeneratedCompliance'})
        self.assertEqual(len(set(gate.PUBLIC.values())), 3)

    def test_changed_bound_tool_refuses_before_stage_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            tool = Path(directory) / 'tool.py'
            tool.write_text('original')
            config = {'bindings': [gate.binding(tool)]}
            gate.unchanged_inputs(config)
            tool.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'frozen gate input changed'):
                gate.unchanged_inputs(config)

    def test_clone_failure_does_not_fall_back_to_a_full_copy(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'source'
            source.write_text('data')
            with patch.object(gate.subprocess, 'run', side_effect=OSError('clone refused')) as run:
                with self.assertRaisesRegex(OSError, 'clone refused'):
                    gate.clone(source, root / 'target')
            self.assertEqual(run.call_count, 1)
            self.assertIn('--reflink=always', run.call_args.args[0])
            self.assertFalse((root / 'target').exists())

    def test_trace_path_cannot_leave_the_owned_workspace(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / 'build/stock-zisk/build-recipe.json'
            manifest.parent.mkdir(parents=True)
            manifest.write_text(json.dumps({'project_derived': {
                'generated/isla-traces/../../../outside.v': {'sha256': '0' * 64}}}))
            with self.assertRaisesRegex(ValueError, 'contained source inputs'):
                gate.stage_traces(root, root)

    def test_unknown_or_missing_trace_bytes_do_not_stage(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / 'build/stock-zisk/build-recipe.json'
            manifest.parent.mkdir(parents=True)
            manifest.write_text(json.dumps({'project_derived': {
                'generated/isla-traces/absent.v': {'sha256': '0' * 64}}}))
            with self.assertRaisesRegex(ValueError, 'supply --trace-source'):
                gate.stage_traces(root, None)

    def test_changed_protected_source_does_not_reuse_a_baseline_object(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            candidate, baseline = root / 'candidate', root / 'baseline'
            candidate.mkdir(); baseline.mkdir()
            (candidate / 'Public.v').write_text('Lemma result : True. Proof. exact I. Qed.\n')
            (baseline / 'Public.v').write_text('Lemma result : False. Admitted.\n')
            with patch.object(gate, 'PUBLIC', {'result': 'Public.v'}):
                with self.assertRaisesRegex(ValueError, 'Protected PUBLIC source changed'):
                    gate.public_records(candidate, baseline, root / 'build')
            self.assertFalse((baseline / '_build').exists())

    def fresh_build(self, root):
        theory = root / 'build/default/ZesuSsz'
        theory.mkdir(parents=True)
        (theory / '.ZesuSsz.theory.d').write_text(
            'A.vo A.glob: A.v B.vo /opam/lib/List.vo \\\n  Sub/C.vo\n'
            'B.vo B.glob: B.v ../generated/D.vo\n'
            'Sub/C.vo: Sub/C.v\n')
        return root / 'build'

    def test_fresh_dependencies_skip_fresh_members_and_installed_libraries(self):
        with tempfile.TemporaryDirectory() as directory:
            build = self.fresh_build(Path(directory))
            self.assertEqual(gate.fresh_dependencies(build, ['ZesuSsz/A.vo', 'ZesuSsz/B.vo']),
                             ['ZesuSsz/Sub/C.vo', 'generated/D.vo'])
            self.assertEqual(gate.fresh_dependencies(build, ['ZesuSsz/A.vo']),
                             ['ZesuSsz/B.vo', 'ZesuSsz/Sub/C.vo'])
            with self.assertRaisesRegex(ValueError, 'lacks a fresh-set module'):
                gate.fresh_dependencies(build, ['ZesuSsz/Absent.vo'])

    @staticmethod
    def atom(value):
        return f'{len(value.encode())}:{value}'

    def finish(self, source, target, exit_code='0', program='.bin/coqc'):
        a = self.atom
        return (f'({a("process")}{a("finish")}(({a("1")}{a("2")}))({a("process_args")}({a("-q")}{a(source)}))'
                f'({a("pid")}{a("7")})({a("prog")}{a(program)})({a("exit")}{a(exit_code)})'
                f'({a("target_files")}({a("_dune-cache/default/" + target)})))')

    def test_trace_must_show_a_successful_coqc_run_for_each_fresh_object(self):
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / 'trace.csexp'
            target = 'ZesuSsz/A.vo'
            trace.write_text(self.finish('ZesuSsz/A.v', target))
            self.assertEqual(gate.fresh_compiler_runs(trace, [target])[target]['source'], 'ZesuSsz/A.v')
            for event in [self.finish('ZesuSsz/A.v', target, exit_code='1'),
                          self.finish('ZesuSsz/A.v', target, program='.bin/coqdep'),
                          self.finish('ZesuSsz/Other.v', target)]:
                trace.write_text(event)
                with self.assertRaisesRegex(ValueError, 'no fresh coqc run'):
                    gate.fresh_compiler_runs(trace, [target])

    def test_receipt_refuses_a_linked_object_that_differs_from_the_fresh_compile(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build, captured, target = root / 'build', root / 'captured', 'ZesuSsz/A.vo'
            (build / 'default/ZesuSsz').mkdir(parents=True)
            (captured / 'ZesuSsz').mkdir(parents=True)
            (build / 'trace.csexp').write_text(self.finish('ZesuSsz/A.v', target))
            (build / 'default' / target).write_bytes(b'object')
            (captured / target).write_bytes(b'object')
            receipt = gate.public_fresh_receipt(build, [target], captured, 0)
            self.assertTrue(receipt['fresh_objects'][0]['equal'])
            (build / 'default' / target).write_bytes(b'cached object')
            with self.assertRaisesRegex(ValueError, 'differs from the fresh compile'):
                gate.public_fresh_receipt(build, [target], captured, 0)
            (captured / target).unlink()
            with self.assertRaisesRegex(ValueError, 'fresh object is missing'):
                gate.public_fresh_receipt(build, [target], captured, 0)


if __name__ == '__main__':
    unittest.main()
