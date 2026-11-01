"""Check complete promotion against the accepted 6974 source history."""
import json
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import complete_promotion

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'ZesuSsz/Evidence'))
import generate_decode_item_native_status as native_status
MODULE = 'ZesuSsz.Proofs.DecodeItem.Auto.Block800d6974'
LEMMA = MODULE + '.DesignedBoundary_800d6974'
INPUTS = [
    'ZesuSsz/Proofs/DecodeItem/Auto/Block800d6974.v',
    'ZesuSsz/Proofs/DecodeItem/TableSlots/Adapter800d6974Conditional.v',
    'ZesuSsz/Generated/DecodeItem/PromotedBodies.v',
    'ZesuSsz/Compliance/DecodeItemCompliance.v',
    'ZesuSsz/Evidence/DecodeItemOpenNativeHypotheses.v',
]
# The accepted history kept the open-hypothesis compliance lemma in a
# Scaffolding alias that the tool now edits in the production module.
HISTORICAL_COMPLIANCE = 'Scaffolding/DecodeItemNativeBlocksCompliance.v'
HISTORICAL_NAMES = {'ZesuSsz/Compliance/DecodeItemCompliance.v': HISTORICAL_COMPLIANCE}


def historical(ref, name):
    return subprocess.check_output(['git', 'show', ref + ':' + name], cwd=ROOT, text=True)


class CompletePromotionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.workspace = Path(self.temp.name)
        for name in INPUTS:
            path = self.workspace / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(historical('cp-p1-i60', HISTORICAL_NAMES.get(name, name)))

    def test_6974_matches_both_accepted_checkpoints(self):
        outputs, provenance = complete_promotion.plan(self.workspace, 0x800d6974, MODULE, LEMMA)
        for name in ['ZesuSsz/Proofs/DecodeItem/TableSlots/Adapter800d6974.v',
                     'ZesuSsz/Generated/DecodeItem/PromotedBodies.v',
                     'ZesuSsz/Evidence/DecodeItemPromoted6974Fixtures.v']:
            expected = historical('cp-p1-s50', name)
            if name.endswith('/PromotedBodies.v'):
                expected = re.sub(r'^Print Assumptions [^\n]+\n', '', expected, flags=re.M).rstrip() + '\n'
            self.assertEqual(outputs[name], expected, name)
        audit = outputs['ZesuSsz/Generated/DecodeItem/PromotedBodiesAssumptions.v']
        self.assertIn('Print Assumptions ZesuSsz.Generated.DecodeItem.PromotedBodies.'
                      'decodeItemPromotedBody800d6974.', audit)
        self.assertEqual(outputs['ZesuSsz/Compliance/DecodeItemCompliance.v'],
                         re.sub(r'^Print Assumptions [^\n]+\n', '',
                                historical('cp-p1-s53', HISTORICAL_COMPLIANCE), flags=re.M))
        self.assertEqual(outputs['ZesuSsz/Compliance/DecodeItemComplianceAssumptions.v'],
                         'Require Import ZesuSsz.Compliance.DecodeItemCompliance.\n\n'
                         'Print Assumptions ZesuSsz.Compliance.DecodeItemCompliance.'
                         'decodeItemNativeBlocksSelectedCompliance.\n')
        self.assertEqual(len(provenance['remaining_native_hypotheses']), 15)
        self.assertNotIn('native800d6974', provenance['remaining_native_hypotheses'])
        self.assertEqual(outputs['ZesuSsz/Evidence/DecodeItemOpenNativeHypotheses.v'].count(
            'native800d6974 :'), 0)
        self.assertIn('length decodeItemOpenNativeBlocks = 15%nat',
                      outputs['ZesuSsz/Evidence/DecodeItemOpenNativeHypotheses.v'])

    def test_missing_named_theorem_is_rejected_before_writes(self):
        before = {name: (self.workspace / name).read_bytes() for name in INPUTS}
        with self.assertRaisesRegex(ValueError, 'named production theorem'):
            complete_promotion.plan(self.workspace, 0x800d6974, MODULE, MODULE + '.Missing')
        self.assertEqual(before, {name: (self.workspace / name).read_bytes() for name in INPUTS})

    def test_promotion_records_the_emitted_audit_in_existing_shape_inventory(self):
        path = self.workspace / 'ZesuSsz/Evidence/spec_shape_inventory.json'
        inventory = {'base_commit': 'preserved', 'modules': {'Existing.v': {'kept': 1}}}
        path.write_text(json.dumps(inventory))
        outputs, _ = complete_promotion.plan(self.workspace, 0x800d6974, MODULE, LEMMA)
        generated = json.loads(outputs['ZesuSsz/Evidence/spec_shape_inventory.json'])
        self.assertEqual(generated['base_commit'], 'preserved')
        self.assertEqual(generated['modules']['Existing.v'], {'kept': 1})
        self.assertEqual(generated['modules']['ZesuSsz/Compliance/DecodeItemComplianceAssumptions.v'],
                         dict.fromkeys(('uninferable_existentials', 'predicates_without_unfold',
                             'disjunctive_specs', 'frame_parameters_in_closed_specs',
                             'unfold_without_typeclasses_opaque'), 0))

    def test_compliance_audit_requires_its_exact_declared_target(self):
        with self.assertRaisesRegex(ValueError, 'audit target is unavailable'):
            complete_promotion.compliance_audit('Lemma another : True. Proof. exact I. Qed.')

    def test_compliance_audit_refuses_foreign_or_undeclared_targets(self):
        source = 'Lemma selected : True. Proof. exact I. Qed.\n'
        for target in ['Project.Other.selected', 'missing']:
            with self.subTest(target=target):
                with self.assertRaisesRegex(ValueError, 'audit target is unavailable'):
                    complete_promotion.compliance_audit(source + f'Print Assumptions {target}.\n')

    def test_existing_slot_reverifies_only_its_recorded_proof(self):
        outputs, _ = complete_promotion.plan(self.workspace, 0x800d6974, MODULE, LEMMA)
        for name, text in outputs.items():
            path = self.workspace / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        repeated, provenance = complete_promotion.plan(self.workspace, 0x800d6974, MODULE, LEMMA)
        self.assertEqual(outputs, repeated)
        self.assertTrue(provenance['already_closed'])
        self.assertIsNone(provenance['native_hypothesis_removed'])
        adapter = self.workspace / 'ZesuSsz/Proofs/DecodeItem/TableSlots/Adapter800d6974.v'
        adapter.write_text(adapter.read_text().replace(f'Require Import {MODULE}.', ''))
        with self.assertRaisesRegex(ValueError, 'recorded production proof'):
            complete_promotion.plan(self.workspace, 0x800d6974, MODULE, LEMMA)

    def test_record_fields_and_destruct_names_match_after_each_removal(self):
        status = 'ZesuSsz/Evidence/DecodeItemOpenNativeHypotheses.v'
        compliance = 'ZesuSsz/Compliance/DecodeItemCompliance.v'
        originals = {name: (self.workspace / name).read_text() for name in INPUTS}
        sites = re.findall(r'^  native800d([0-9a-f]+)\s*:', originals[status], re.M)
        cases = [('first', sites[0], sites), ('middle', sites[len(sites) // 2], sites),
                 ('last', sites[-1], sites), ('final', sites[0], sites[:1])]
        for label, selected, open_sites in cases:
            with self.subTest(removal=label):
                for name, source in originals.items():
                    (self.workspace / name).write_text(source)
                if label == 'final':
                    text = originals[status]
                    record = ('Record DecodeItemOpenNativeHypotheses : Prop := {\n'
                              f'  native800d{selected} : decodeItemOpenNativeClosure{selected}\n}}.')
                    text = re.sub(r'Record DecodeItemOpenNativeHypotheses : Prop := \{.*?\n\}\.',
                                  record, text, flags=re.S)
                    text = re.sub(r'  destruct Hopen as \[[^\]]*\]\.',
                                  f'  destruct Hopen as [H{selected}].', text)
                    (self.workspace / status).write_text(text)
                    text = originals[compliance]
                    for site in sites[1:]:
                        text = complete_promotion.remove_binders(text, 'native800d' + site)
                    (self.workspace / compliance).write_text(text)
                pc = int('800d' + selected, 16)
                production = self.workspace / INPUTS[0]
                production.write_text(originals[INPUTS[0]].replace('instr_body 0x800d6974',
                                                                  'instr_body ' + hex(pc)))
                conditional = self.workspace / f'ZesuSsz/Proofs/DecodeItem/TableSlots/Adapter{pc:x}Conditional.v'
                conditional.write_text(originals[INPUTS[1]])
                outputs, provenance = complete_promotion.plan(self.workspace, pc, MODULE, LEMMA)
                remaining = [site for site in open_sites if site != selected]
                text = outputs[status]
                self.assertEqual(re.findall(r'^  native800d([0-9a-f]+)\s*:', text, re.M), remaining)
                names = re.search(r'  destruct Hopen as \[([^\]]*)\]\.', text)[1].split()
                self.assertEqual(names, ['H' + site for site in remaining])
                self.assertNotRegex(text, r'\(H' + selected + r' Sigma islaG0 H\)')
                self.assertEqual(provenance['remaining_native_hypotheses'],
                                 ['native800d' + site for site in remaining])

    def test_generated_dependencies_precede_their_consumers(self):
        outputs, _ = complete_promotion.plan(self.workspace, 0x800d6974, MODULE, LEMMA)
        positions = {name[:-2].replace('/', '.'): index
                     for index, name in enumerate(outputs)}
        for index, (name, source) in enumerate(outputs.items()):
            for module in re.findall(r'^Require Import ([A-Za-z0-9_.]+)\.', source, re.M):
                if module in positions:
                    self.assertLess(positions[module], index, (name, module))

    def test_promoted_imports_follow_recorded_proof_modules(self):
        module = 'ZesuSsz.Proofs.DecodeItem.TableSlots.RecordedAdapter'
        original = ('Require Import Unrelated.Module.\n'
                    'Definition decodeItemPromotedBody800d6974 :\n'
                    '  True :=\n  ' + module + '.recordedProof.\n')
        source = complete_promotion.update_promoted(original, 0x800d6b08)
        imports = set(re.findall(r'^Require Import ([A-Za-z0-9_.]+)\.', source, re.M))
        common = set(re.findall(r'^Require Import ([A-Za-z0-9_.]+)\.',
                                complete_promotion.PREFIX, re.M))
        self.assertEqual(imports, common | {module,
            'ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6b08'})
        self.assertIn(module + '.recordedProof.', source)
        terms = re.findall(r':=\s*([A-Za-z0-9_.]+)\.\s', source)
        self.assertEqual({term.rsplit('.', 1)[0] for term in terms}, imports - common)

    def test_unavailable_recorded_proof_term_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'recorded promoted proof terms'):
            complete_promotion.update_promoted(
                'Definition decodeItemPromotedBody800d6974 : True := I.\n', 0x800d6b08)

    def test_execution_capture_is_not_a_named_module(self):
        with self.assertRaises(ValueError):
            complete_promotion.plan(self.workspace, 0x800d6974, 'Boundary', 'Boundary.closed')

    def test_wrong_block_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'conditional adapter|different block'):
            complete_promotion.plan(self.workspace, 0x800d697c, MODULE, LEMMA)

    def test_all_unrelated_native_hypotheses_remain_exact(self):
        outputs, _ = complete_promotion.plan(self.workspace, 0x800d6974, MODULE, LEMMA)
        original = (self.workspace / 'ZesuSsz/Compliance/DecodeItemCompliance.v').read_text()
        for site in ['6960', '697c', '698c', '69b0', '69e8', '6a08', '6a24', '6a38',
                     '6a40', '6a78', '6aa8', '6ac4', '6ad8', '6ae0', '6b08']:
            name = 'native800d' + site
            removed = complete_promotion.remove_binders(original, name)
            start = original.rfind('  (', 0, original.index(name))
            # The removed declaration is the exact substring missing from the
            # balanced-binder removal. Check its presence in the final source.
            end = start + len(original) - len(removed)
            self.assertIn(original[start:end], outputs['ZesuSsz/Compliance/DecodeItemCompliance.v'])

    def status_table(self, broken=False):
        production = self.workspace / INPUTS[0]
        source_sha = complete_promotion.binding(production)['sha256']
        sites = ['6960', '6974', '697c', '698c', '69b0', '69e8', '6a08', '6a24',
                 '6a38', '6a40', '6a78', '6aa8', '6ac4', '6ad8', '6ae0', '6b08']
        table = self.workspace / 'build/stock-zisk/table.json'
        table.parent.mkdir(parents=True)
        table.write_text(json.dumps({'root': native_status.MEASUREMENT_ROOT,
            'approved_switches': 28, 'hint_modules': 25, 'rows': [
                {'block': '0x800d' + site, 'goal_count': None,
                 'source': str(production), 'source_sha256': 'wrong' if broken else source_sha,
                 'statement_sha256': 'fixture', 'outcome': 'limit-stop', 'captures': []}
                for site in sites]}))
        return table

    def test_complete_command_updates_every_consumer_and_status(self):
        table = self.status_table()
        with patch.object(native_status, 'I67_SHA256', complete_promotion.binding(table)['sha256']), \
             patch.object(complete_promotion.subprocess, 'check_output', return_value='fixture-root\n'), \
             patch('promotion_verification.verify_generated', return_value={'success': True}) as verifier:
            report = complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                                                  self.workspace / 'report.json', table)
        self.assertEqual(report['native_status']['open_closures'], 15)
        self.assertEqual(report['native_status']['closed_6974']['theorem'], LEMMA)
        self.assertEqual(len(report['generated_sources']), 7)
        self.assertTrue(report['success'])
        self.assertEqual(report['status'], 'verified')
        verifier.assert_called_once()
        self.assertEqual(len(verifier.call_args.args[1]), 7)
        self.assertEqual((self.workspace / INPUTS[2]).read_text(),
                         re.sub(r'^Print Assumptions [^\n]+\n', '',
                                historical('cp-p1-s50', INPUTS[2]), flags=re.M).rstrip() + '\n')

    def test_dry_run_emits_without_verification_or_success(self):
        table = self.status_table()
        with patch.object(native_status, 'I67_SHA256', complete_promotion.binding(table)['sha256']), \
             patch.object(complete_promotion.subprocess, 'check_output', return_value='fixture-root\n'), \
             patch('promotion_verification.verify_generated') as verifier:
            report = complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                self.workspace / 'report.json', table, dry_run=True)
        verifier.assert_not_called()
        self.assertFalse(report['success'])
        self.assertEqual(report['status'], 'dry_run')
        self.assertNotIn('kernel_verification_required', report)
        self.assertEqual(len(report['generated_sources']), 7)

    def test_failed_verification_restores_sources_and_reports_failure(self):
        table = self.status_table()
        before = {name: (self.workspace / name).read_bytes() for name in INPUTS}
        with patch.object(native_status, 'I67_SHA256', complete_promotion.binding(table)['sha256']), \
             patch.object(complete_promotion.subprocess, 'check_output', return_value='fixture-root\n'), \
             patch('promotion_verification.verify_generated', side_effect=ValueError('MCP verification failed')), \
             self.assertRaisesRegex(ValueError, 'MCP verification failed'):
            complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                self.workspace / 'report.json', table)
        self.assertEqual(before, {name: (self.workspace / name).read_bytes() for name in INPUTS})
        report = json.loads((self.workspace / 'report.json').read_text())
        self.assertFalse(report['success'])
        self.assertEqual(report['status'], 'verification_failed')
        self.assertTrue(report['sources_restored'])
        self.assertFalse((self.workspace / 'ZesuSsz/Proofs/DecodeItem/TableSlots/Adapter800d6974.v').exists())

    def test_existing_report_is_preserved_before_source_emission(self):
        output = self.workspace / 'report.json'
        output.write_text('reviewed bytes')
        before = {name: (self.workspace / name).read_bytes() for name in INPUTS}
        with self.assertRaisesRegex(ValueError, 'evidence already exists'):
            complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                                        output, self.status_table())
        self.assertEqual(output.read_text(), 'reviewed bytes')
        self.assertEqual(before, {name: (self.workspace / name).read_bytes() for name in INPUTS})

    def test_existing_verification_is_preserved_before_source_emission(self):
        directory = self.workspace / 'prior-verification'
        directory.mkdir()
        before = {name: (self.workspace / name).read_bytes() for name in INPUTS}
        with self.assertRaisesRegex(ValueError, 'evidence already exists'):
            complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                self.workspace / 'report.json', self.status_table(), verification_directory=directory)
        self.assertEqual(before, {name: (self.workspace / name).read_bytes() for name in INPUTS})

    def test_bad_status_source_rolls_back_all_source_updates(self):
        table = self.status_table(broken=True)
        before = {name: (self.workspace / name).read_bytes() for name in INPUTS}
        with patch.object(native_status, 'I67_SHA256', complete_promotion.binding(table)['sha256']), \
             patch.object(complete_promotion.subprocess, 'check_output', return_value='fixture-root\n'), \
             self.assertRaisesRegex(ValueError, 'measured source hash differs'):
            complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                                        self.workspace / 'report.json', table)
        self.assertEqual(before, {name: (self.workspace / name).read_bytes() for name in INPUTS})
        self.assertFalse((self.workspace / 'report.json').exists())
        self.assertFalse((self.workspace / 'ZesuSsz/Proofs/DecodeItem/TableSlots/Adapter800d6974.v').exists())

    def test_missing_history_still_verifies_sources_and_records_reason(self):
        status = self.workspace / INPUTS[4]
        status.write_text(status.read_text() +
            '\nDefinition decodeItemI67NativeResidualCounts : list (Z * option nat) :=\n'
            '  [(0x800d6974, Some 3%nat); (0x800d697c, None)].\n')
        reason = 'The retained historical table is unavailable.'
        with patch.object(complete_promotion.subprocess, 'check_output', return_value='fixture-root\n'), \
             patch.object(native_status, 'generate', side_effect=AssertionError('historical access')), \
             patch('promotion_verification.verify_generated', return_value={'success': True}) as verifier:
            report = complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                self.workspace / 'report.json', self.workspace / 'missing-table.json',
                no_historical_evidence=True, reason=reason)
        self.assertTrue(report['success'])
        self.assertIsNone(report['native_status'])
        self.assertEqual(report['historical_evidence'], {'checked': False, 'reason': reason})
        self.assertIn(reason, (self.workspace / 'tools/block/PROMOTION.md').read_text())
        self.assertNotIn('(0x800d6974, Some', status.read_text())
        self.assertIn('(0x800d697c, None)', status.read_text())
        verifier.assert_called_once()
        self.assertEqual(len(verifier.call_args.args[1]), 7)
        self.assertTrue(all(path.suffix == '.v' for path in verifier.call_args.args[1]))

    def test_history_skip_requires_explicit_reason(self):
        for reason in (None, '', '  '):
            with self.subTest(reason=reason), self.assertRaisesRegex(ValueError, 'nonempty reason'):
                complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                    self.workspace / 'report.json', None, no_historical_evidence=True, reason=reason)
        with self.assertRaisesRegex(ValueError, 'explicit skip flag'):
            complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                self.workspace / 'report.json', None, reason='Unavailable')
        with self.assertRaisesRegex(ValueError, 'I67 table hash differs'):
            complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                self.workspace / 'report.json', None)

    def test_history_skip_restores_documentation_after_failed_verification(self):
        documentation = self.workspace / 'tools/block/PROMOTION.md'
        documentation.parent.mkdir(parents=True)
        documentation.write_text('Existing instructions.\n')
        before = {name: (self.workspace / name).read_bytes() for name in INPUTS}
        with patch.object(complete_promotion.subprocess, 'check_output', return_value='fixture-root\n'), \
             patch('promotion_verification.verify_generated', side_effect=ValueError('MCP refused')), \
             self.assertRaisesRegex(ValueError, 'MCP refused'):
            complete_promotion.complete(self.workspace, 0x800d6974, MODULE, LEMMA,
                self.workspace / 'report.json', None, no_historical_evidence=True, reason='Unavailable')
        self.assertEqual(documentation.read_text(), 'Existing instructions.\n')
        self.assertEqual(before, {name: (self.workspace / name).read_bytes() for name in INPUTS})
        report = json.loads((self.workspace / 'report.json').read_text())
        self.assertEqual(report['status'], 'verification_failed')
        self.assertFalse(report['success'])



class EdgeAdapterTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.workspace = Path(self.temp.name)
        path = self.workspace / "Fixture/Contracts.v"
        path.parent.mkdir()
        path.write_text("Definition root := True.\nDefinition source := True.\n"
                        "Definition selected := True.\nDefinition sum := True.\n")
        source_hashes = {"Fixture/Contracts.v": complete_promotion.binding(path)["sha256"]}
        def row(pc, name, binders, successors):
            return {"entry_pc": hex(pc), "entry_definition": "Fixture.Contracts." + name,
                    "resource_predicate": "Fixture.Contracts." + name,
                    "binders": binders, "arguments": [item["name"] for item in binders],
                    "source_hashes": source_hashes, "successor_pcs": list(map(hex, successors)),
                    "incoming_edges": []}
        shared = {"name": "args", "type": "unit"}
        root = row(0x1000, "root", [shared], [0x1004])
        source = row(0x1004, "source", [shared, {"name": "loaded", "type": "nat"}], [0x1008])
        self.target = row(0x1008, "sum", [shared, {"name": "value", "type": "nat"}], [])
        self.edge = {"from_block": "0x1004", "from_instruction": "0x1004",
                     "resource_alternative": "Fixture.Contracts.selected"}
        self.target["incoming_edges"] = [self.edge]
        self.design = {"entry_pc": "0x1000", "blocks": [root, source, self.target]}

    def render(self, **kwargs):
        return complete_promotion.render_adapter(0x1004, "Fixture.Proof", "native",
            ["args", "loaded"], design=self.design, workspace=self.workspace, **kwargs)

    def test_selected_alternative_uses_wand_without_changing_table_interface(self):
        source = self.render()
        self.assertIn('instr_body 0x1004 decodeItemState1004.', source)
        self.assertIn('instr_pre_wand with "Hnext1008 []"', source)
        self.assertIn('iApply (native args loaded with "[Hnext1008] Hcode")', source)
        self.assertIn('iAssert (Fixture.Contracts.selected (args) (next1008_value))%I', source)
        self.assertIn('iExists next1008_value.', source)
        self.assertNotIn('iExists args', source)
        self.assertIn('rewrite /Fixture.Contracts.sum.', source)
        self.assertIn('Require Import Fixture.Contracts.', source)
        self.assertNotIn('Definition decodeItemEdge', source)

    def test_absent_field_preserves_accepted_adapter_bytes(self):
        del self.edge["resource_alternative"]
        plain = complete_promotion.render_adapter(0x1004, "Fixture.Proof", "native", ["args", "loaded"])
        self.assertEqual(self.render().encode(), plain.encode())
        self.assertIn('exact (native args loaded).', plain)

    def test_unrelated_predecessor_does_not_trigger_adaptation(self):
        self.edge["from_block"] = "0x1000"
        self.assertNotIn('instr_pre_wand', self.render())

    def test_missing_selected_declaration_is_rejected(self):
        self.edge["resource_alternative"] = "Fixture.Contracts.absent"
        with self.assertRaisesRegex(ValueError, 'lacks Definition'):
            self.render()

    def test_changed_bound_source_is_rejected(self):
        (self.workspace / "Fixture/Contracts.v").write_text('Definition selected := False.')
        with self.assertRaisesRegex(ValueError, 'source hash changed'):
            self.render()

    def test_undeclared_successor_is_rejected(self):
        self.design["blocks"][1]["successor_pcs"] = []
        with self.assertRaisesRegex(ValueError, 'undeclared successor'):
            self.render()

    def test_duplicate_alternative_for_one_successor_is_rejected(self):
        self.target["incoming_edges"].append(dict(self.edge))
        with self.assertRaisesRegex(ValueError, 'repeats a resource alternative'):
            self.render()

    def test_changed_native_arguments_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'native arguments differ'):
            complete_promotion.render_adapter(0x1004, "Fixture.Proof", "native", ["loaded", "args"],
                design=self.design, workspace=self.workspace)

    def test_changed_shared_parameter_type_is_rejected(self):
        self.target["binders"] = [{"name": "args", "type": "nat"}]
        self.target["arguments"] = ["args"]
        with self.assertRaisesRegex(ValueError, 'shared successor parameter'):
            self.render()

    def test_parameter_free_resource_does_not_create_a_witness(self):
        self.target["binders"] = []
        self.target["arguments"] = []
        source = self.render()
        self.assertIn('iIntros "Hentry".', source)
        self.assertNotIn('iExists', source)

    def test_proposition_witness_is_rejected(self):
        self.target["binders"][1]["type"] = "Prop"
        with self.assertRaisesRegex(ValueError, 'not a data parameter'):
            self.render()



if __name__ == '__main__':
    unittest.main()
