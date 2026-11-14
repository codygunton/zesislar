import json
import tempfile
import unittest
from pathlib import Path

from call_boundary import CallRefused, call_return_seed, interface_of
import check_proved_functions as C
import render_interfaces as R

REGISTRY = {'functions': [{
    'function': 'callee', 'symbol': 'lib.callee', 'status': 'proved', 'compliance_theorems': ['calleeCompliance'],
    'owned_prefixes': ['ZesuSsz/Contracts/Callee', 'ZesuSsz/Generated/Callee/'],
    'interface': {'module': 'ZesuSsz.Interfaces.Callee', 'sealed_module': 'CalleeSealed', 'requires': [],
                  'exports': ['ZesuSsz.Contracts.CalleeData'],
                  'correct': {'module': 'ZesuSsz.Interfaces.CalleeCorrect', 'requires': [], 'exports': [],
                              'premises': [], 'code': 'calleeCode', 'entry': 'calleeEntry',
                              'template_correct': 'calleeTemplateCorrect'}},
    'call_spec': {'name': 'calleeCallSpec2', 'template': 'calleeTemplate',
                  'template_source': 'ZesuSsz/Contracts/CalleeSpec.v', 'correct_from': 'calleeCorrectFrom'},
    'sealed': [{'name': 'calleeMeaning', 'type': 'nat -> Prop', 'definition': 'CalleeMeaning'}],
    'interface_lemmas': [{'name': 'calleeMeaningSmall', 'binders': 'n', 'premise': 'calleeMeaning n',
                          'conclusion': 'n < 3', 'proof': 'calleeMeaningSmallProof', 'derived_facts': True}]}]}
CALL = {'callee_pc': 'lib.callee+0x0', 'spec': 'calleeCallSpec2', 'spec_module': 'ZesuSsz.Interfaces.Callee',
        'spec_source': 'ZesuSsz/Interfaces/Callee.v'}


class InterfaceCallTests(unittest.TestCase):
    def test_a_call_through_the_interface_is_accepted(self):
        self.assertEqual(interface_of(CALL, REGISTRY)['function'], 'callee')

    def test_a_call_to_an_internal_spec_is_refused(self):
        internal = dict(CALL, spec_module='ZesuSsz.Contracts.CalleeSpec', spec_source='ZesuSsz/Contracts/CalleeSpec.v')
        with self.assertRaises(CallRefused):
            interface_of(internal, REGISTRY)

    def test_an_unregistered_callee_is_unconstrained(self):
        other = dict(CALL, callee_pc='lib.other+0x0', spec='otherCallSpec2', spec_module='M', spec_source='M.v')
        self.assertIsNone(interface_of(other, REGISTRY))

    def test_the_generator_refuses_before_reading_the_spec(self):
        internal = dict(CALL, spec_module='ZesuSsz.Contracts.CalleeSpec', spec_source='missing.v')
        registry = json.loads((C.ROOT / 'ZesuSsz/Contracts/proved_functions.json').read_text())
        entry = next(row for row in registry['functions'] if row.get('interface'))
        internal['callee_pc'] = entry['symbol'] + '+0x0'
        with self.assertRaises(CallRefused):
            call_return_seed([{'state': {}}], call=internal, function_root=C.ROOT, root_seed=None, shapes=None,
                             vocabulary=None)


class InterfaceRenderTests(unittest.TestCase):
    def test_the_signature_seals_and_the_module_realizes(self):
        entry = REGISTRY['functions'][0]
        with tempfile.TemporaryDirectory() as root:
            source = Path(root) / 'ZesuSsz/Contracts/CalleeSpec.v'
            source.parent.mkdir(parents=True)
            source.write_text('Definition calleeTemplate := (machine_call m 16 (fun argv sp RET => '
                              '⌜CalleeMeaning 1⌝ ∗ RET (fun _ => True)))%I.\n')
            old = R.ROOT
            R.ROOT = Path(root)
            try:
                text = R.interface_text(entry)
            finally:
                R.ROOT = old
        self.assertIn('Module Type CalleeSealedSignature.\n  Parameter calleeMeaning : nat -> Prop.', text)
        self.assertIn('Module CalleeSealed : CalleeSealedSignature.', text)
        self.assertIn('  Definition calleeMeaning : nat -> Prop := CalleeMeaning.', text)
        self.assertIn('  Axiom calleeMeaningSmall : forall n, calleeMeaning n -> n < 3.', text)
        self.assertIn('  Definition calleeMeaningSmall := calleeMeaningSmallProof.', text)
        self.assertIn('⌜calleeMeaning 1⌝', text.split('Definition calleeCallSpec2 ')[1])
        self.assertIn('#[export] Instance calleeMeaningSmallDerivedFacts n', text)

    def test_committed_interfaces_are_fresh(self):
        self.assertEqual(R.stale(), [])


class ProvedFunctionCheckTests(unittest.TestCase):
    def write(self, root, path, text):
        target = Path(root) / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def test_a_caller_requiring_an_internal_module_fails(self):
        with tempfile.TemporaryDirectory() as root:
            self.write(root, 'ZesuSsz/Contracts/CalleeSpec.v', '')
            self.write(root, 'ZesuSsz/Contracts/CalleeData.v', '')
            self.write(root, 'ZesuSsz/Automation2/Rule.v',
                       'Require Import ZesuSsz.Contracts.CalleeData.\n(* Require Import ZesuSsz.Contracts.CalleeSpec. *)\n')
            self.write(root, 'ZesuSsz/Compliance/OtherComposition.v', 'From ZesuSsz Require Import Contracts.CalleeSpec.\n')
            (Path(root) / 'tools/block/functions').mkdir(parents=True)
            self.assertEqual(C.import_violations(REGISTRY, Path(root)), [
                'ZesuSsz/Compliance/OtherComposition.v: requires ZesuSsz.Contracts.CalleeSpec, an internal module '
                'of the proved function callee; import ZesuSsz.Interfaces.Callee'])

    def test_an_unregistered_compliance_theorem_fails(self):
        with tempfile.TemporaryDirectory() as root:
            self.write(root, 'ZesuSsz/Compliance/Other.v',
                       'Theorem otherGeneratedCompliance : True.\nLemma calleeCompliance : True.\n')
            self.assertEqual(C.coverage_violations(REGISTRY, Path(root)), [
                'ZesuSsz/Compliance/Other.v: compliance theorem otherGeneratedCompliance has no entry in '
                'ZesuSsz/Contracts/proved_functions.json'])

    def test_the_repository_passes(self):
        self.assertEqual(C.violations(), [])


if __name__ == '__main__':
    unittest.main()
