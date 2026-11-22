"""Profile key `array_spelling`: how an owned stored array of the forward state is written."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from fractional_source import FractionalSourceArrays
import entry_hist

DECLARATION = {'owner': 'isla.ghost_state', 'name': 'mem_mapsto_array_def',
               'arguments': ['implicit n : N', 'a : Z', 'q : dfrac', 'l : list (bv n)']}


def plain(record, context):
    return [{'kind': 'plain', 'source': record['source']}]


def adapt(source, **keys):
    adapter = FractionalSourceArrays(plain, declaration=DECLARATION, **keys)
    return adapter({'id': 'r', 'source': source}, {}), adapter.applications


class ArraySpelling(unittest.TestCase):
    def configure(self, **keys):
        entry_hist.configure({'entry_hist': 'wrap', **keys})
        self.addCleanup(entry_hist.configure, {'entry_hist': 'wrap'})

    def test_the_default_is_the_definition(self):
        self.configure()
        self.assertEqual(entry_hist.ARRAY_SPELLING, 'definition')
        result, applications = adapt('(a + 8) ↦ₘ{DfracOwn 1}∗ ([x; y])')
        self.assertEqual(result[0]['kind'], 'application')
        self.assertEqual(result[0]['predicate']['name'], 'mem_mapsto_array_def')
        self.assertEqual(len(applications), 1)

    def test_sealed_writes_the_notation(self):
        self.configure(array_spelling='sealed')
        self.assertEqual(entry_hist.ARRAY_SPELLING, 'sealed')
        result, applications = adapt('(a + 8) ↦ₘ{DfracOwn 1}∗ ([x; y])', seal_owned=True)
        self.assertEqual(result, [{'kind': 'plain', 'source': '((a + 8)) ↦ₘ∗ (([x; y]))'}])
        self.assertEqual(applications, [])

    def test_sealed_keeps_other_fractions_on_the_definition(self):
        result, applications = adapt('(a) ↦ₘ{DfracOwn (1/2)}∗ ([x])', seal_owned=True)
        self.assertEqual(result[0]['kind'], 'application')
        self.assertEqual(len(applications), 1)

    def test_unknown_spelling_is_refused(self):
        with self.assertRaises(ValueError):
            entry_hist.configure({'entry_hist': 'wrap', 'array_spelling': 'cells'})
        entry_hist.configure({'entry_hist': 'wrap'})


if __name__ == '__main__':
    unittest.main()
