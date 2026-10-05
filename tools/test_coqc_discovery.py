import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent/'block'))
import coqc_discovery


class CoqcDiscoveryTests(unittest.TestCase):
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
