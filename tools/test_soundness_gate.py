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
                         'd13ef899c73649d078654cb983d537048a443ce7a8d81b45990d5d9017916580')

    def test_wrapper_generator_stays_outside_the_production_shape_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            workspace = Path(directory)
            out = workspace / '_build/agents/test-gate'
            out.mkdir(parents=True)
            build = out / 'build'
            source, artifact = gate.wrapper_paths(workspace, out, build)
            calls = []

            async def verify(root, sources, pc, report, **kwargs):
                calls.append(list(sources))
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
            'decodeItemSelectedComplianceCompositional', 'decodeItemSlotBody800d698c'})
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


if __name__ == '__main__':
    unittest.main()
