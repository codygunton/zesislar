"""Source identity controls do not manufacture proof acceptance receipts."""
from copy import deepcopy
from pathlib import Path
import hashlib
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from join_refutations import refute_entry_edges, validate_source_edge


class SourceEdgeTests(unittest.TestCase):
    def setUp(self):
        self.value = {'op': 'bits', 'width': 64, 'value': 0}
        self.row = {'path': [0, 1], 'state': {'registers': {},
                    'retained_registers': {'x13': self.value}, 'conditions': [{'op': 'bool', 'value': True}]}}
        self.edge = {'path': [0, 1], 'original_conditions': deepcopy(self.row['state']['conditions']),
                     'original_values': {'x13': deepcopy(self.value)}}

    def test_exact_retained_value_is_the_producer_projection(self):
        validate_source_edge(self.row, self.edge)

    def test_current_register_overrides_retained_value(self):
        self.row['state']['registers']['x13'] = {'op': 'bits', 'width': 64, 'value': 1}
        with self.assertRaisesRegex(ValueError, 'owned source value'):
            validate_source_edge(self.row, self.edge)

    def test_same_name_wrong_width_refuses(self):
        self.row['state']['retained_registers']['x13'] = {'op': 'bits', 'width': 32, 'value': 0}
        with self.assertRaisesRegex(ValueError, 'owned source value'):
            validate_source_edge(self.row, self.edge)

    def test_changed_source_guard_refuses(self):
        self.row['state']['conditions'] = []
        with self.assertRaisesRegex(ValueError, 'another source edge'):
            validate_source_edge(self.row, self.edge)

    def test_changed_source_path_refuses(self):
        self.row['path'] = [1, 0]
        with self.assertRaisesRegex(ValueError, 'another source edge'):
            validate_source_edge(self.row, self.edge)

    def boundary_binding(self, directory):
        def save(name, value):
            path = Path(directory) / name
            path.write_text(json.dumps(value))
            return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
        plan = {'edges': [{'index': 0, **deepcopy(self.edge)}]}
        reference = save('binding.json', {'schema': 'source.edge-refutation-binding.v1',
            'plan': save('plan.json', plan), 'refutations': []})
        return {'pc': '0x20', 'alternatives': [deepcopy(self.row)]}, reference

    def test_empty_refutations_preserve_the_complete_source_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            boundary, reference = self.boundary_binding(directory)
            before = deepcopy(boundary)
            result = refute_entry_edges(boundary, reference)
            self.assertEqual(result['alternatives'], boundary['alternatives'])
            self.assertEqual(result['source_edge_refutations']['excluded_indices'], [])
            self.assertEqual(boundary, before)

    def test_refutation_plan_rejects_another_edge_count(self):
        with tempfile.TemporaryDirectory() as directory:
            boundary, reference = self.boundary_binding(directory)
            boundary['alternatives'].append(deepcopy(self.row))
            with self.assertRaisesRegex(ValueError, 'edge count'):
                refute_entry_edges(boundary, reference)

    def test_refutation_plan_rejects_another_source_projection(self):
        with tempfile.TemporaryDirectory() as directory:
            boundary, reference = self.boundary_binding(directory)
            boundary['alternatives'][0]['state']['conditions'] = []
            with self.assertRaisesRegex(ValueError, 'another source edge'):
                refute_entry_edges(boundary, reference)

    def test_refutation_plan_rejects_changed_bound_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            boundary, reference = self.boundary_binding(directory)
            (Path(directory) / 'plan.json').write_text('{}')
            with self.assertRaisesRegex(ValueError, 'binding changed'):
                refute_entry_edges(boundary, reference)
