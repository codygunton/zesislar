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
            self.assertEqual(outputs[name], historical('cp-p1-s50', name), name)
        self.assertEqual(outputs['ZesuSsz/Compliance/DecodeItemCompliance.v'],
                         historical('cp-p1-s53', HISTORICAL_COMPLIANCE))
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
        self.assertEqual(len(report['generated_sources']), 5)
        self.assertTrue(report['success'])
        self.assertEqual(report['status'], 'verified')
        verifier.assert_called_once()
        self.assertEqual(len(verifier.call_args.args[1]), 5)
        self.assertEqual((self.workspace / INPUTS[2]).read_text(),
                         historical('cp-p1-s50', INPUTS[2]))

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
        self.assertEqual(len(report['generated_sources']), 5)

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


if __name__ == '__main__':
    unittest.main()
