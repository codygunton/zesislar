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
                              'template_correct': 'calleeTemplateCorrect'},
                  'goal_domain_unfold': ['CalleeDomain']},
    'call_spec': {'name': 'calleeCallSpec2', 'template': 'calleeTemplate',
                  'template_source': 'ZesuSsz/Contracts/CalleeSpec.v', 'correct_from': 'calleeCorrectFrom'},
    'sealed': [{'name': 'calleeMeaning', 'type': 'nat -> Prop', 'definition': 'CalleeMeaning'}],
    'interface_lemmas': [{'name': 'calleeMeaningSmall', 'binders': 'n', 'premise': 'calleeMeaning n',
                          'conclusion': 'n < 3', 'proof': 'calleeMeaningSmallProof', 'derived_facts': True},
                         {'name': 'calleeMeaningIntro', 'binders': 'n', 'premise': 'CalleeDomain n',
                          'conclusion': 'calleeMeaning n', 'proof': 'calleeMeaningIntroProof',
                          'derived_facts': False, 'goal_domain_intro': True}]}]}
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
        self.assertNotIn('calleeMeaningIntroDerivedFacts', text)
        self.assertIn('#[export] Instance calleeMeaningIntroGoalDomain n :\n'
                      '  ZesuGoalDomainIntro (calleeMeaning n)\n    (CalleeDomain n) :=\n  calleeMeaningIntro n.', text)
        self.assertIn('#[export] Hint Unfold CalleeDomain : zesu_goal_domain.', text)

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

    def test_a_charged_variant_of_the_function_is_no_caller(self):
        with tempfile.TemporaryDirectory() as root:
            self.write(root, 'ZesuSsz/Contracts/CalleeSpec.v', '')
            source = 'Require Import ZesuSsz.Contracts.CalleeSpec.\n'
            self.write(root, 'ZesuSsz/Generated/CalleeBudget/Entries.v', source)
            self.write(root, 'ZesuSsz/Generated/Other/Entries.v', source)
            self.write(root, 'tools/block/functions/calleeBudget.json', json.dumps(
                {'function': 'calleeBudget', 'symbol': 'lib.callee',
                 'generated_directory': 'ZesuSsz/Generated/CalleeBudget'}))
            self.write(root, 'tools/block/functions/other.json', json.dumps(
                {'function': 'other', 'symbol': 'lib.other', 'generated_directory': 'ZesuSsz/Generated/Other'}))
            self.assertEqual(C.import_violations(REGISTRY, Path(root)), [
                'ZesuSsz/Generated/Other/Entries.v: requires ZesuSsz.Contracts.CalleeSpec, an internal module '
                'of the proved function callee; import ZesuSsz.Interfaces.Callee'])

    def test_an_unregistered_compliance_theorem_fails(self):
        with tempfile.TemporaryDirectory() as root:
            self.write(root, 'ZesuSsz/Compliance/Other.v',
                       'Theorem otherGeneratedCompliance : True.\nLemma calleeCompliance : True.\n')
            self.assertEqual(C.coverage_violations(REGISTRY, Path(root)), [
                'ZesuSsz/Compliance/Other.v: compliance theorem otherGeneratedCompliance has no entry in '
                'ZesuSsz/Contracts/proved_functions.json'])

    def test_a_new_legacy_caller_is_refused_outside_frozen_modules(self):
        rows = [{'path': 'ZesuSsz/Compliance/Other.v', 'module': 'ZesuSsz.Contracts.CalleeSpec', 'reason': 'r'},
                {'path': 'ZesuSsz/Automation/Old.v', 'module': 'ZesuSsz.Contracts.CalleeSpec', 'reason': 'r'},
                {'path': 'ZesuSsz/Proofs/Tests/ClassR.v', 'module': 'ZesuSsz.Contracts.CalleeSpec', 'reason': 'r'},
                {'path': 'ZesuSsz/Compliance/NextUint64CallBridge.v',
                 'module': 'ZesuSsz.Contracts.DecodeItemCompositional', 'reason': ''}]
        registry = {'functions': [dict(REGISTRY['functions'][0], legacy_callers=rows)]}
        with tempfile.TemporaryDirectory() as root:
            self.write(root, 'ZesuSsz/Evidence/hygiene_baseline.json',
                       json.dumps({'legacy_entry_files': ['ZesuSsz/Proofs/Tests/ClassR.v']}))
            self.assertEqual(C.legacy_admission_violations(registry, Path(root)), [
                'callee: new legacy caller ZesuSsz/Compliance/Other.v (ZesuSsz.Contracts.CalleeSpec) refused: only '
                'a frozen ZesuSsz/Automation/ module or a frozen class-R module may be listed; import '
                'ZesuSsz.Interfaces.Callee',
                'callee: legacy caller ZesuSsz/Compliance/NextUint64CallBridge.v lists no reason'])

    def test_an_assumed_premise_row_names_its_definitions(self):
        row = {'function': 'alloc', 'symbol': 'alloc', 'status': 'assumed', 'compliance_theorems': [],
               'owned_prefixes': [], 'premise': {'module': 'ZesuSsz.Contracts.AllocPremise',
                                                 'name': 'allocCallPremise', 'call_spec': 'allocCallSpec'}}
        with tempfile.TemporaryDirectory() as root:
            self.write(root, 'ZesuSsz/Contracts/AllocPremise.v', 'Definition allocCallSpec := True.\n')
            self.assertEqual(C.premise_violations(row, Path(root)), [
                'alloc: ZesuSsz.Contracts.AllocPremise does not define allocCallPremise'])
            self.assertEqual(C.premise_violations(dict(row, premise={'module': 'ZesuSsz.Contracts.AllocPremise'}),
                                                  Path(root)),
                             ['alloc: an assumed row without an interface names premise {module, name, call_spec}'])

    def test_a_charged_row_names_its_declarations(self):
        names = {'contract': 'CalleeBudgetContractCorrect', 'compliance': 'calleeBudgetCompliance',
                 'code': 'calleeChargedCode', 'call_spec_correct': 'calleeBudgetCallSpec2_correct'}
        charged = {key: {'module': 'ZesuSsz.Contracts.CalleeBudget', 'name': name} for key, name in names.items()}
        row = dict(REGISTRY['functions'][0], budget=7, charged=charged,
                   compliance_theorems=['calleeCompliance', 'calleeBudgetCompliance'])
        with tempfile.TemporaryDirectory() as root:
            self.write(root, 'ZesuSsz/Contracts/CalleeBudget.v',
                       'Definition CalleeBudgetContractCorrect := True.\nTheorem calleeBudgetCompliance : True.\n'
                       'Definition calleeChargedCode := True.\n(* Lemma calleeBudgetCallSpec2_correct *)\n')
            self.assertEqual(C.charged_violations(row, Path(root)), [
                'callee: ZesuSsz.Contracts.CalleeBudget does not declare calleeBudgetCallSpec2_correct'])
            self.assertEqual(C.charged_violations(dict(row, budget='7'), Path(root)), [
                'callee: a charged row has an integer budget and charged '
                '{call_spec_correct, code, compliance, contract}'])

    def test_the_repository_passes(self):
        self.assertEqual(C.violations(), [])


if __name__ == '__main__':
    unittest.main()
