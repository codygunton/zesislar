"""Accept only the existing exact explicit full-memory fraction syntax."""
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).parent / 'block'))
from witness_data import _array_owners, resolved_array_value
from forward_witnesses import _check_forward_owner
import hashlib


class JoinWitnessFractionTests(unittest.TestCase):
    source = 'Definition source : iProp Sigma := (10) ↦ₘ{DfracOwn 1}∗ bytes.\n'

    def test_exact_full_fraction_preserves_assertion_and_payload(self):
        source = self.source
        owners = _array_owners(source, 'source')
        self.assertEqual(source, self.source)
        self.assertEqual(owners[0]['fraction'], {'term': 'DfracOwn 1', 'source': '{DfracOwn 1}'})
        self.assertEqual(owners[0]['value'], 'bytes')
        self.assertEqual(owners[0]['address'], ['10'])
        self.assertIsNone(_array_owners(source.replace('{DfracOwn 1}', ''), 'source')[0]['fraction'])

    def test_projection_retains_the_exact_explicit_fraction(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Owner.v';path.write_text(self.source)
            before = path.read_bytes()
            binding = {'path': str(path), 'sha256': hashlib.sha256(before).hexdigest(), 'declaration': 'source'}
            row = {'resources': [{'kind': 'byte_array', 'address': '(10)', 'value': 'bytes'}]}
            projected = _check_forward_owner(row, binding)
            self.assertEqual(projected['array_fractions'], [
                {'address': '(10)', 'fraction': {'term': 'DfracOwn 1', 'source': '{DfracOwn 1}'}}])
            target = 'Definition target : iProp Sigma := ∃ (frame : list byte), (10) ↦ₘ∗ frame.'
            self.assertEqual(resolved_array_value(target, 'target', 'frame', binding), 'bytes')
            self.assertEqual(path.read_bytes(), before)

    def test_changed_symbolic_discarded_malformed_and_partial_fractions_refuse(self):
        for fraction in ['DfracOwn 2', 'DfracOwn q', 'DfracDiscarded', 'DfracBoth 1',
                         'DfracOwn (1/2)', 'DfracOwn (1)', '', 'DfracOwn 01', 'DfracOwn 1%Qp']:
            with self.subTest(fraction=fraction), self.assertRaises(ValueError):
                _array_owners(self.source.replace('DfracOwn 1', fraction), 'source')
        for source in [self.source.replace('}∗', '}'), self.source.replace('}∗', '∗'),
                       self.source.replace('↦ₘ{DfracOwn 1}∗', '↦ₘ∗{q}')]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                _array_owners(source, 'source')


if __name__ == '__main__':unittest.main()
