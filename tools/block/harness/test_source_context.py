"""Resolve colliding source imports without changing compiler mappings."""
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import scratch
from installed_mappings import InstalledMappings


class SourceContextTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.sail = self.root / 'sail-stdpp'
        self.sail.mkdir()
        project = Path(scratch.__file__).resolve().parents[3]
        self.base = self.sail / 'Base.v'
        self.base.write_bytes((project / 'generated/sail-stdpp/Base.v').read_bytes())
        self.string = self.sail / 'String.v'
        self.string.write_bytes((project / 'generated/sail-stdpp/String.v').read_bytes())
        # The resolver inspects paths only. This object is explicit unit data.
        self.string.with_suffix('.vo').write_bytes(b'unit dependency object')
        self.coq = Path(os.environ['OPAM_SWITCH_PREFIX']) / 'lib/coq/theories'
        self.byte_vector = self.coq / 'Strings/ByteVector.v'
        self.flags = ['-R', str(self.coq), 'Coq', '-Q', str(self.sail), 'SailStdpp']

    def installed(self, receipt_name='receipts'):
        value = InstalledMappings(self.flags, receipt_dir=self.root / receipt_name)
        value.register_source(self.byte_vector.read_text(), self.byte_vector)
        value.register_source(self.base.read_text(), self.base)
        return value

    def test_actual_string_sources_resolve_independently_in_both_orders(self):
        expected = {self.byte_vector: (self.coq / 'Strings/String.v', 'Coq.Strings.String'),
                    self.base: (self.string, 'SailStdpp.String')}
        for index, order in enumerate([(self.byte_vector, self.base), (self.base, self.byte_vector)]):
            with self.subTest(order=order):
                installed = self.installed('receipts-' + str(index))
                flags = list(installed.flags)
                for origin in order:
                    answer = installed.resolution('String', origin=origin)
                    self.assertEqual((answer['source'], answer['canonical']), expected[origin])
                with self.assertRaisesRegex(ValueError, 'graph name ambiguously: String'):
                    installed.resolve('String')
                with patch.object(installed, '_query', side_effect=AssertionError('unexpected query')):
                    for origin in reversed(order):
                        self.assertEqual(installed.resolve('String', origin=origin), expected[origin][0])
                receipts = [json.loads(path.read_text()) for path in (self.root / ('receipts-' + str(index))).glob('*.json')]
                self.assertEqual({row['request']['origin']['path'] for row in receipts},
                                 {str(self.base), str(self.byte_vector)})
                self.assertTrue(all(row['returncode'] == 0 and row['stderr'] == '' for row in receipts))
                self.assertEqual(installed.flags, flags)
                self.assertEqual(self.flags[-3:], ['-Q', str(self.sail), 'SailStdpp'])

    def test_changed_source_refuses_before_memory_cache_hit(self):
        installed = self.installed()
        installed.resolve('String', origin=self.base)
        self.base.write_bytes(self.base.read_bytes() + b'\n')
        with patch.object(installed, '_query', side_effect=AssertionError('unexpected query')):
            with self.assertRaisesRegex(ValueError, 'request source changed'):
                installed.resolve('String', origin=self.base)

    def test_unregistered_source_refuses(self):
        installed = self.installed()
        source = self.sail / 'Unknown.v'
        source.write_text('Require Import String.\n')
        with self.assertRaisesRegex(ValueError, 'not registered'):
            installed.resolve('String', origin=source)

    def test_source_without_request_cannot_use_another_sources_answer(self):
        installed = self.installed()
        source = self.sail / 'Empty.v'
        source.write_text('Definition empty := 0.\n')
        installed.register_source(source.read_text(), source)
        installed.resolve('String', origin=self.base)
        with self.assertRaisesRegex(ValueError, 'no matching Require request'):
            installed.resolve('String', origin=source)

    def test_canonical_edges_use_the_exact_source_bound_answer(self):
        installed = self.installed()
        for parent, canonical in [(self.sail, 'SailStdpp.String'), (self.root, 'Coq.Strings.String')]:
            source = parent / 'Consumer.v'
            source.write_text('Require Import String.\n')
            edges = scratch.canonical_edges('Consumer', source.read_text(), None, [], {}, installed, source)
            self.assertEqual(edges, [{'from': 'Consumer', 'to': canonical}])
            key = ('String', str(source), hashlib.sha256(source.read_bytes()).hexdigest())
            self.assertEqual(installed.context_resolutions[key]['canonical'], canonical)


if __name__ == '__main__':
    unittest.main()
