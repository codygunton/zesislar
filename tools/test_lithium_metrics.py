"""Tests for commit-bound Lithium source counts."""

import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import lithium_metrics


class CountingTests(unittest.TestCase):
    def test_ranges_merge_overlaps(self):
        self.assertEqual(lithium_metrics.range_count(['a', 'b', 'c'], [[1, 2], [2, 3]]), 3)

    def test_range_outside_file_is_rejected(self):
        for ranges in ([[0, 1]], [[2, 1]], [[1, 4]]):
            with self.subTest(ranges=ranges), self.assertRaises(ValueError):
                lithium_metrics.range_count(['a', 'b', 'c'], ranges)

    def test_priority_and_mixed_count(self):
        counts, mixed, structural = lithium_metrics.classify_lines(['liAStep; iFrame; lia.'])
        self.assertEqual(counts['machine'], 1)
        self.assertEqual(sum(counts.values()), 1)
        self.assertEqual(mixed, 1)
        self.assertEqual(structural, 0)

    def test_structural_line_inherits_next_then_previous_kind(self):
        counts, mixed, structural = lithium_metrics.classify_lines(['{', 'iFrame.', '}', ''])
        self.assertEqual(counts['spatial'], 3)
        self.assertEqual(sum(counts.values()), 3)
        self.assertEqual(structural, 2)
        self.assertEqual(mixed, 0)

    def test_unmatched_line_is_other(self):
        counts, _, _ = lithium_metrics.classify_lines(['unknown_tactic.', '}'])
        self.assertEqual(counts['other'], 2)

    def test_two_tokens_from_one_kind_are_not_mixed(self):
        counts, mixed, _ = lithium_metrics.classify_lines(['iFrame; iRename "x" into "y".'])
        self.assertEqual(counts['spatial'], 1)
        self.assertEqual(mixed, 0)

    def test_tokens_match_complete_names(self):
        counts, _, _ = lithium_metrics.classify_lines(['my_liAStep_helper.', 'iFrame.'])
        self.assertEqual(counts['machine'], 0)
        self.assertEqual(counts['other'], 1)
        self.assertEqual(counts['spatial'], 1)

    def test_final_structural_line_falls_back_to_other(self):
        counts, _, structural = lithium_metrics.classify_lines(['{', '}'])
        self.assertEqual(counts['other'], 2)
        self.assertEqual(structural, 2)

    def test_report_preserves_existing_metrics(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'metrics.json'
            output.write_text(json.dumps({'blocks': {'example': 4}}))
            with patch.object(lithium_metrics, 'Commit'), \
                    patch.object(lithium_metrics, 'count_commit', return_value={'commit': 'abc'}), \
                    patch('builtins.print'):
                self.assertEqual(lithium_metrics.main(['--output', str(output)]), 0)
            result = json.loads(output.read_text())
            self.assertEqual(result['blocks'], {'example': 4})
            self.assertEqual(result['m2_by_commit'], {'abc': {'commit': 'abc'}})

    def test_call_spec_glue_is_counted_once_with_or_without_manifest_entry(self):
        root = Path(__file__).resolve().parents[1]
        baseline = lithium_metrics.Commit(root, '33f27d9a')
        original = lithium_metrics.count_commit(baseline)
        path = 'ZesuSsz/Compliance/DecodeItemCallSpec.v'
        contents = b'Lemma example : True.\nProof. exact I.\nQed.\n'
        class Overlay:
            sha = baseline.sha
            paths = baseline.paths | {path}
            def __init__(self, listed):
                self.listed = listed
            def read(self, selected):
                if selected == path:
                    return contents
                data = baseline.read(selected)
                if selected == lithium_metrics.MANIFEST and self.listed:
                    manifest = json.loads(data)
                    manifest['files'].append(dict(path=path, category='composition', scope='whole_file'))
                    return json.dumps(manifest).encode()
                return data
        for listed in (False, True):
            with self.subTest(listed=listed):
                report = lithium_metrics.count_commit(Overlay(listed))
                self.assertEqual(report['other_proof_text_lines'], original['other_proof_text_lines'] + 3)
                self.assertEqual(len(report['call_spec_glue']), len(original['call_spec_glue']) + (0 if listed else 1))

    def test_new_function_module_requires_manifest_classification(self):
        root = Path(__file__).resolve().parents[1]
        baseline = lithium_metrics.Commit(root, '33f27d9a')
        class Overlay:
            sha = baseline.sha
            paths = baseline.paths | {'ZesuSsz/Compliance/DecodeItemNewFacts.v'}
            read = baseline.read
        with self.assertRaisesRegex(ValueError, 'manifest omits a module'):
            lithium_metrics.count_commit(Overlay())

    def test_recorded_baseline_block_and_line_counts(self):
        root = Path(__file__).resolve().parents[1]
        report = lithium_metrics.count_commit(lithium_metrics.Commit(root, '33f27d9a'))
        self.assertEqual(report['blocks']['total'], 24)
        self.assertEqual(report['blocks']['native'], 11)
        self.assertEqual(report['blocks']['hand'], 13)
        self.assertEqual(report['hand_suffix_lines'], 1033)
        self.assertEqual(report['automation_lines'], 8254)
        self.assertEqual(report['other_proof_text_lines'], 12620)
        self.assertEqual(report['m2_total_lines'], 13653)
        self.assertEqual(report['function_text_categories'], {
            'contracts': 2497, 'introductions': 3688, 'exit_meanings': 3114,
            'loop_steps': 965, 'registrations': 343, 'generator_json': 6299,
            'block_proofs': 3467, 'composition': 371, 'tests_and_exports': 35435})
        self.assertIn('ZesuSsz/Contracts/NextUint64Selected.v', report['changed_mixed_manifest_files'])
        self.assertEqual(report['hand_suffix_kinds'], {
            'machine': 54, 'trace_return': 7, 'encoding': 29, 'branch': 302,
            'spatial': 102, 'finishing': 197, 'other': 342})
        self.assertEqual(report['mixed_lines'], 340)
        self.assertEqual(sum(report['hand_suffix_kinds'].values()), 1033)
        self.assertEqual(report['kind_counts_label'], 'kind counts v2 (replacement classifier, 2026-10-19)')


if __name__ == '__main__':
    unittest.main()
