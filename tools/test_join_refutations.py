"""Source identity controls do not manufacture proof acceptance receipts."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from join_refutations import validate_source_edge


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
