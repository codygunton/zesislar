import hashlib
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent/'block'))
import coqc_primary
import coqc_certificate
import json
import tempfile


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
