"""A call argument closed inside a call's carried facts never shares a name with a register binder.

The automation picks a successor's register witness by name: a call-argument binder named like a
register binder of another entry (machine_x13) is a stale namesake of that register's value."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
GENERATED = ROOT / 'ZesuSsz/Generated'
BINDER = re.compile(r"\((\w[\w']*) : [^()]*\)")
TELESCOPE = re.compile(r"⌜\(∃ ((?:\(\w[\w']* : [^()]*\) ?)+),")
REGISTER = re.compile(r"\"x\d+\" ↦ᵣ \(?RVal_Bits \((\w[\w']*) : bv 64%N\)")


def entry_names(text):
    """(call-argument binders, register binders) of one rendered entries module."""
    arguments = {name for telescope in TELESCOPE.findall(text) for name in BINDER.findall(telescope)}
    return arguments, set(REGISTER.findall(text))


class CallArgumentBinders(unittest.TestCase):
    def test_entry_names_reads_both_binder_kinds(self):
        text = ('(∃ (machine_x13 : bv 64), "x13" ↦ᵣ RVal_Bits (machine_x13 : bv 64%N) ∗ '
                '⌜(∃ (call2_arg_x13 : bv 64) (before : list byte), P call2_arg_x13 before)⌝)')
        self.assertEqual(entry_names(text), ({'call2_arg_x13', 'before'}, {'machine_x13'}))

    def test_no_rendered_entry_binds_a_call_argument_under_a_register_binder_name(self):
        modules = sorted(GENERATED.glob('*/FP301/*Entries.v'))
        self.assertTrue(modules)
        for function in sorted({path.parent for path in modules}):
            arguments, registers = {}, set()
            for path in function.glob('*Entries.v'):
                found, bound = entry_names(path.read_text())
                for name in found:
                    arguments.setdefault(name, path.name)
                registers |= bound
            shared = sorted(set(arguments) & registers)
            self.assertEqual(shared, [], '%s: %s' % (function.parent.name,
                                                     ', '.join('%s (%s)' % (name, arguments[name]) for name in shared)))


if __name__ == '__main__':
    unittest.main()
