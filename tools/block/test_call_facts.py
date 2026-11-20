"""A call's carried facts: spec definitions the entries import stay folded (design
`folded_definitions`), and a lookup in the literal argument list is the argument it reads, so the
record binds no argument register that it does not read."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from call_boundary import (CallRefused, _argv_lookups, _atoms, _unfold, _unfolded_definitions,
                           parse_machine_call_spec)

ROOT = Path(__file__).resolve().parents[2]
SOURCE = 'ZesuSsz/Contracts/ParentHeaderMemcpyService.v'
CALL = {'spec': 'memcpyCallSpec2', 'spec_source': SOURCE}
ARGUMENTS = ['(parentHeaderResultPointer args)', '(BV 64%N 2148618168%Z)', '(BV 64%N 80%Z)',
             '(machine_x13)', '(machine_x14)', '(machine_x15)', '(machine_x16)', '(machine_x17)']


def carried(call):
    text = (ROOT / SOURCE).read_text()
    spec = parse_machine_call_spec(text, call['spec'])
    raw = spec['pre']['facts'] + spec['post']['facts']
    local = _unfolded_definitions(call, text, _atoms(' '.join(raw)))
    return [_argv_lookups(_unfold(fact, local), spec['names']['argv'], ARGUMENTS) for fact in raw]


class FoldedDefinitions(unittest.TestCase):
    def test_a_folded_definition_stays_folded_and_the_others_unfold(self):
        unfolded = ' '.join(carried(CALL))
        self.assertNotIn('parentHeaderMemcpyDomain', unfolded)
        self.assertIn('ziskMemcpyRange', unfolded)
        folded = carried({**CALL, 'folded_definitions': ['parentHeaderMemcpyDomain']})
        self.assertIn('parentHeaderMemcpyDomain (bv_unsigned (parentHeaderResultPointer args))', folded)
        self.assertNotIn('ziskMemcpyRange', ' '.join(folded))

    def test_a_folded_name_that_the_spec_file_does_not_define_is_refused(self):
        with self.assertRaises(CallRefused):
            carried({**CALL, 'folded_definitions': ['parentHeaderNoSuchDomain']})


class ArgumentLookups(unittest.TestCase):
    def test_a_lookup_in_the_argument_list_is_that_argument(self):
        self.assertEqual(_argv_lookups('bv_unsigned (argv !!! 1%nat) = c', 'argv', ['(a)', '(b)']),
                         'bv_unsigned (b) = c')
        self.assertEqual(_argv_lookups('P argv !!! 0%nat', 'argv', ['(a)']), 'P (a)')
        # Out of range, another list, or the whole list: unchanged.
        self.assertEqual(_argv_lookups('Q (argv !!! 2%nat) (xargv !!! 0%nat) argv', 'argv', ['(a)']),
                         'Q (argv !!! 2%nat) (xargv !!! 0%nat) argv')

    def test_the_memcpy_record_reads_no_unused_argument_register(self):
        facts = ' '.join(carried({**CALL, 'folded_definitions': ['parentHeaderMemcpyDomain']}))
        self.assertNotIn('!!!', facts)
        for register in ('machine_x13', 'machine_x14', 'machine_x15', 'machine_x16', 'machine_x17'):
            self.assertNotIn(register, facts)


if __name__ == '__main__':
    unittest.main()
