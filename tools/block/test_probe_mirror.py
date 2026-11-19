"""Check the stepping-only probe of a committed generated caller (tools/block/probe_mirror.py)."""
import contextlib
import io
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import probe_mirror as P  # noqa: E402

CALLER = P.ROOT / 'tools/block/generated/nextuint64_fp301_callers/Caller0064.v'


def definition(text, name):
    match = re.search(r'^Definition %s .*?:= (.*)%%I\.$' % name, text, re.M)
    return match.group(1)


class Probe(unittest.TestCase):
    def test_stepping_only_variant(self):
        source = CALLER.read_text()
        with tempfile.TemporaryDirectory() as name:
            with contextlib.redirect_stdout(io.StringIO()) as out:
                P.main(['--output-dir', name, str(CALLER)])
            probe = Path(name) / 'nextuint64_fp301_callers' / 'Probe0064.v'
            text = probe.read_text()
        self.assertIn('pre:', out.getvalue())
        self.assertNotIn('ZesuSsz.Generated', text)  # entries are local copies, their imports dropped
        self.assertTrue(text.endswith(source[source.index('Proof.'):]))  # the caller's own proof
        self.assertIn('instr_pre 0x800d62e4 (succ0_P (args) (returnAddress) (K))%I', text)
        self.assertIn('((pre_P (args) (returnAddress) (K)) ∗', text)
        for name in ('pre_c0', 'pre_P', 'succ0_c0', 'succ0_P'):
            self.assertIn('#[export] Instance %s_unfold : LithiumUnfold (@%s) := I.' % (name, name), text)
            self.assertIn('#[export] Typeclasses Opaque %s.' % name, text)
            self.assertIn('ZesuPureFactIntro Sigma (%s (args) (returnAddress)' % name, text)
        self.assertNotIn('⌜', definition(text, 'succ0_c0'))  # successors state no pure fact
        precondition = definition(text, 'pre_c0')
        self.assertIn('⌜', precondition)
        self.assertNotIn('bool_decide', precondition)  # history facts deleted, domain facts kept
        self.assertEqual(definition(text, 'pre_P'), '(pre_c0 (args) (returnAddress) ∗ K)')

    def test_domain_facts(self):
        binders = {'x'}
        self.assertTrue(P.is_domain('0 <= returnAddress < 2 ^ 64', binders))
        self.assertTrue(P.is_domain('List.length x = 8', binders))  # a length, even of a binder
        self.assertFalse(P.is_domain('bv_unsigned x < 8', binders))
        self.assertFalse(P.is_domain('bool_decide (0 < 1) = true', binders))

    def test_prune_keeps_spatial_parts(self):
        stats = {'pure': 0, 'kept': 0}
        body = '(∃ (x : bv 64), (a ↦ₘ x ∗ ⌜bv_unsigned x < 8 /\\ 0 < 1⌝ ∗ (b ↦ₘ{DfracOwn 1}∗ [x] ∗ ⌜x = x⌝)))'
        pruned = P.prune(body, P.is_domain, stats)
        self.assertEqual(pruned, '(∃ (x : bv 64), (a ↦ₘ x ∗ ⌜(0 < 1)⌝ ∗ (b ↦ₘ{DfracOwn 1}∗ [x])))')
        self.assertEqual(stats, {'pure': 3, 'kept': 1})


if __name__ == '__main__':
    unittest.main()
