import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent/'block'))
import coqc_discovery


class CoqcDiscoveryTests(unittest.TestCase):
    def test_import_targets_keep_qualified_names_and_reject_empty_selection(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            for name in ('ZesuSsz/Automation/All.v','ZesuSsz/Contracts/Entry.v'):
                path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('')
            source='Require Import ZesuSsz.Automation.All ZesuSsz.Contracts.Entry.\n'
            self.assertEqual(coqc_discovery.native_import_targets([source],root),
                ['ZesuSsz/Automation/All.vo','ZesuSsz/Contracts/Entry.vo'])
            with self.assertRaisesRegex(ValueError,'zero targets'):
                coqc_discovery.native_import_targets(['Require Import Unknown.Module.\n'],root)
    def test_changed_automation_selection_includes_every_entry(self):
        baseline={'blocks':[{'entry':hex(i),'outcomes':['primary-unavailable']
            if i<12 else ['native-residual']} for i in range(24)]}
        self.assertEqual(len(coqc_discovery.selection(baseline,True)),24)
        self.assertEqual(len(coqc_discovery.selection(baseline,False)),12)
        baseline['blocks'][0]['outcomes']=['native-residual']
        with self.assertRaisesRegex(ValueError,'exactly12'):
            coqc_discovery.selection(baseline,False)
    def test_archive_binding_precedes_baseline_reuse(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            raw = root/'raw.json'
            raw.write_text(json.dumps({'blocks': [{} for _ in range(24)], 'contract_closures': 0}))
            retained = root/'retained.json'
            retained.write_text(json.dumps({'raw_report': {'archive_path': str(raw),
                'sha256': hashlib.sha256(raw.read_bytes()).hexdigest()}}))
            self.assertEqual(len(coqc_discovery.load_baseline(retained)['blocks']), 24)
            raw.write_text(raw.read_text()+' ')
            with self.assertRaisesRegex(ValueError, 'archive differs'):
                coqc_discovery.load_baseline(retained)

    def test_reuse_requires_identical_statement_budget_and_capture(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, log, capture = root/'source.v', root/'log', root/'capture.json'
            source.write_text('frozen instrumented source')
            log.write_text('frozen compiler result')
            rendered = {'source': 'native source', 'statement_sha256': 'statement'}
            evidence = {'original_source_sha256': hashlib.sha256(b'native source').hexdigest(),
                'statement_sha256': 'statement', 'primary_timeout': 300,
                'primary_tactic_entered': True, 'source': str(source), 'log': str(log),
                'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
            capture.write_text(json.dumps(evidence))
            self.assertEqual(coqc_discovery.checked_reuse(capture, rendered), evidence)
            for field, value in [('primary_timeout', 299), ('primary_tactic_entered', False),
                                 ('statement_sha256', 'different')]:
                capture.write_text(json.dumps({**evidence, field: value}))
                with self.assertRaisesRegex(ValueError, 'different native inputs'):
                    coqc_discovery.checked_reuse(capture, rendered)
            capture.write_text(json.dumps(evidence))
            log.write_text('changed result')
            with self.assertRaisesRegex(ValueError, 'capture changed'):
                coqc_discovery.checked_reuse(capture, rendered)

    def test_module_completion_limits_are_explicit_and_entry_bound(self):
        values = coqc_discovery.module_limits(['0x800d6a24:2400:6', '0x800d698c:1200:12'])
        self.assertEqual(values['0x800d6a24']['cpu_seconds'], 2400)
        self.assertEqual(values['0x800d698c']['memory_kib'], 12582912)
        for invalid in (['0x800d6974:2400:6'], ['0x800d6a24:1200:12'],
                        ['0x800d6a24:2400:6', '0x800d6a24:1200:6']):
            with self.assertRaises(ValueError):
                coqc_discovery.module_limits(invalid)
