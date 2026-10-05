import hashlib
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent/'block'))
import coqc_primary
import coqc_certificate
import json
import tempfile
from unittest.mock import patch
import subprocess


class CoqcPrimaryTests(unittest.TestCase):
    def rendered(self):
        statement = 'Lemma Boundary : selectedCode -∗ instr_body 0x10 actualEntry.'
        return {'source': statement+'\nProof.\ntry zesu_block.\nQed.\nPrint Assumptions Boundary.\n',
                'lemma': 'Boundary', 'entry_pc': '0x10', 'entry_definition': 'Contracts.actualEntry',
                'scope': 'unproved native designed boundary',
                'statement_sha256': hashlib.sha256(statement.encode()).hexdigest()}

    def test_recorder_preserves_statement_and_requests_exact_primary_budget(self):
        rendered = self.rendered()
        source = coqc_primary.instrument(rendered)
        statement = source[source.index('Lemma Boundary'):source.index('\nProof.\n')]
        self.assertEqual(hashlib.sha256(statement.encode()).hexdigest(), rendered['statement_sha256'])
        self.assertEqual(source.count('Timeout 300 try zesu_block.'), 1)
        self.assertIn('Show Existentials.\nQed.', source)
        self.assertNotIn('Unshelve.', source)
        self.assertNotIn('Abort.', source)

    def test_non_native_or_changed_statement_is_rejected(self):
        for update in ({'scope': 'capture entailment only'}, {'entry_pc': '0x20'},
                       {'statement_sha256': '0'*64}, {'entry_definition': None}):
            with self.assertRaisesRegex(ValueError, 'signature is unavailable'):
                coqc_primary.instrument({**self.rendered(), **update})

    def test_changed_primary_and_excess_budget_are_rejected(self):
        rendered = self.rendered()
        rendered['source'] = rendered['source'].replace('try zesu_block.', 'exact I.')
        with self.assertRaisesRegex(ValueError, 'unchanged tactic'):
            coqc_primary.instrument(rendered)
        with self.assertRaisesRegex(ValueError, 'budget'):
            coqc_primary.instrument(self.rendered(), 301)

    def test_missing_or_nonempty_assumption_certificate_cannot_verify(self):
        self.assertFalse(coqc_primary.assumptions_result('', 'Boundary')['verified'])
        self.assertFalse(coqc_primary.assumptions_result('Axioms:\nunsound : False', 'Boundary')['verified'])
        self.assertFalse(coqc_primary.assumptions_result('Closed under the global context\nAxioms:', 'Boundary')['verified'])
        self.assertEqual(coqc_primary.assumptions_result('Closed under the global context', 'Boundary')['assumptions'], [])

    def test_existing_recorder_is_reused_without_redefinition(self):
        rendered = self.rendered()
        rendered['source'] = coqc_primary.chain_goals.RECORDER + rendered['source']
        instrumented = coqc_primary.instrument(rendered)
        self.assertEqual(instrumented.count('Ltac chain_print_environment '), 1)
        self.assertEqual(instrumented.count('Ltac chain_print_goal '), 1)

    def test_complete_fields_recover_missing_final_end_markers(self):
        first = 'CHAIN-GOAL-BEGIN "active"\nCHAIN-GOAL-ENV coq CHAIN-FIELD-END\nCHAIN-GOAL-CONCLUSION True CHAIN-FIELD-END\n'
        second = first.replace('True', 'False') + 'CHAIN-GOAL-END\n'
        self.assertEqual([g['conclusion'] for g in coqc_primary.decode_active(first+second)], ['True', 'False'])
        with self.assertRaisesRegex(ValueError, 'terminated conclusion'):
            coqc_primary.decode_active(first.replace('True CHAIN-FIELD-END', 'True'))

    def test_diagnostic_local_definitions_keep_their_bodies_without_weakening_default_parser(self):
        output = ('CHAIN-GOAL-BEGIN active\n'
            'CHAIN-GOAL-LOCAL LET : nat CHAIN-FIELD-END\n'
            'CHAIN-GOAL-SORT LET : Set CHAIN-FIELD-END\n'
            'CHAIN-GOAL-VALUE LET : 3 + 4 CHAIN-FIELD-END\n'
            'CHAIN-GOAL-ENV coq CHAIN-FIELD-END\n'
            'CHAIN-GOAL-CONCLUSION LET = 7 CHAIN-FIELD-END\nCHAIN-GOAL-END\n')
        with self.assertRaisesRegex(ValueError, 'unresolved native local definitions'):
            coqc_primary.chain_goals.parse_goals(output)
        goals = coqc_primary.decode_active(output)
        self.assertEqual(goals[0]['local_values'], {'LET': '3 + 4'})
        self.assertIn('LET := 3 + 4 : nat', goals[0]['context'])

    def test_missing_primary_or_recorder_keeps_active_group_unavailable(self):
        self.assertIsNone(coqc_primary.diagnostic_active('Error: inconsistent assumptions'))
        self.assertIsNone(coqc_primary.diagnostic_active('COQC-PRIMARY-BEGIN\nproof limit exceeded: time'))
        self.assertEqual(coqc_primary.diagnostic_active(
            'COQC-PRIMARY-BEGIN\nChars 1 - 2 [Show~Existentials.] 0.01 secs'), [])

    def test_native_certificate_requires_kernel_artifact_and_no_inherited_debts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            rendered = {**self.rendered(), 'successors': ['0x20']}
            source, log, artifact = root/'proof.v', root/'log', root/'proof.vo'
            source.write_text(coqc_primary.instrument(rendered))
            log.write_text('Closed under the global context')
            artifact.write_bytes(b'test artifact')
            evidence = {'compiler': {'exit_code': 0, 'limit': None,
                'compiled_object': {'path': str(artifact), 'sha256': coqc_primary.digest(artifact)}},
                'native_qed_compiled': True, 'inherited_debts': {}, 'primary_tactic_entered': True,
                'primary_tactic': 'try zesu_block.', 'primary_timeout': 300,
                'original_source_sha256': hashlib.sha256(rendered['source'].encode()).hexdigest(),
                'statement_sha256': rendered['statement_sha256'],
                'entry_definition': rendered['entry_definition'], 'successors': rendered['successors'],
                'source': str(source), 'source_sha256': coqc_primary.digest(source),
                'log': str(log), 'log_sha256': coqc_primary.digest(log),
                'assumption_verification': {'verified': True, 'assumptions': []}}
            self.assertTrue(coqc_certificate.native_closed(evidence, rendered))
            for update in ({'inherited_debts': {'shelf': ['debt']}}, {'primary_timeout': 299},
                           {'native_qed_compiled': False}, {'successors': ['0x30']},
                           {'assumption_verification': {'verified': True, 'assumptions': ['axiom']}}):
                self.assertFalse(coqc_certificate.native_closed({**evidence, **update}, rendered))
            artifact.write_bytes(b'changed object')
            self.assertFalse(coqc_certificate.native_closed(evidence, rendered))


class CompletionBudgetTests(unittest.TestCase):
    rendered = CoqcPrimaryTests.rendered
    def test_cpu_instrumentation_preserves_tactic_without_wall_timeout(self):
        source = coqc_primary.instrument(self.rendered(), cpu_seconds=1200)
        self.assertNotIn('Timeout ', source)
        self.assertIn('\ntry zesu_block.\n', source)
        self.assertIn('Show Existentials.\nQed.', source)
        for invalid in (0, 1201, -1, 1.5):
            with self.assertRaisesRegex(ValueError, 'CPU budget'):
                coqc_primary.instrument(self.rendered(), cpu_seconds=invalid)

    def test_completion_compile_sets_both_monitors_and_cpu_guard(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root/'Profile.v'
            source.write_text('Set Ltac Profiling.\n')
            policy = coqc_primary.budget_policy(cpu_seconds=1200)
            with patch.object(coqc_primary.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, '', '')) as run:
                coqc_primary.compile_source(source, root/'out', root/'build', policy=policy)
            environment = run.call_args.kwargs['env']
            self.assertEqual(environment['ZESU_PRIMARY_CPU_LIMIT'], '1200')
            self.assertEqual(environment['ZESU_PROOF_CPU_LIMIT'], '1200')
            self.assertEqual(environment['ZESU_PRIMARY_WALL_LIMIT'], 'none')
            self.assertEqual(environment['ZESU_SCRATCH_WALL_SECONDS'], 'none')
            self.assertEqual(source.read_text(), 'Set Ltac Profiling.\n')

    def test_certificate_cpu_policy_requires_matching_compiler_limits(self):
        policy = coqc_primary.budget_policy(cpu_seconds=1200)
        evidence = {'proof_budget': policy, 'primary_timeout': None}
        compiler = {'limits': {'cpu_seconds': 1200, 'module_seconds': None, 'rss_kib': 6291456}}
        self.assertTrue(coqc_certificate.valid_budget(evidence, compiler))
        for field, value in (('cpu_seconds', 300), ('module_seconds', 300), ('rss_kib', 0)):
            changed = {'limits': {**compiler['limits'], field: value}}
            self.assertFalse(coqc_certificate.valid_budget(evidence, changed))

    def test_default_budget_remains_historical_wall_policy(self):
        self.assertEqual(coqc_primary.budget_policy(), {'kind': 'wall', 'cpu_seconds': None,
            'wall_seconds': 300, 'memory_kib': 6291456})
        self.assertEqual(coqc_primary.completion_environment(coqc_primary.budget_policy())['ZESU_SCRATCH_WALL_SECONDS'], '300')
