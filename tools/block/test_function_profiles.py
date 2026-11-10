"""Check that the renderers read every function-specific value from a profile."""
import json
import re
from pathlib import Path
import tempfile
import unittest

from function_profiles import FunctionProfile, load_profile, loop_header, pilot_header, return_header
from render_fp301_statements import (
    render_block_caller,
    return_precondition,
    selected_loop_declaration,
    successor_precondition,
)

ROOT = Path(__file__).resolve().parents[2]


def other_profile():
    data = json.loads((ROOT / 'tools/block/functions/decodeItem.json').read_text())
    data.update({
        'function': 'otherFunction',
        'args_type': 'OtherArgs',
        'generated_directory': 'ZesuSsz/Generated/Other/FP301',
        'callers_directory': 'tools/block/generated/other_callers',
        'contract_requires': ['Require Import ZesuSsz.Contracts.OtherContract.'],
        'loop_contract_requires': ['Require Import ZesuSsz.Contracts.OtherContract.'],
        'caller_contract_requires': ['Require Import ZesuSsz.Contracts.OtherContract.'],
        'selected_code': {'module': 'ZesuSsz.Contracts.OtherSelected', 'premise': 'otherSelectedCode'},
        'caller_hint_umbrella': 'ZesuSsz.Compliance.OtherHints',
        'domain_component': '⌜otherDomain args⌝',
        'blocks': ['1000', '1010'],
        'loop_heads': [],
    })
    for key in ['loop_head_fixture', 'loop_first_pass', 'loop_exits', 'loop_successors']:
        data.pop(key)
    return FunctionProfile(data)


class DecodeItemProfile(unittest.TestCase):
    """The decodeItem profile reproduces the committed headers and callers."""

    def test_headers_open_the_committed_outputs(self):
        profile = load_profile()
        directory = ROOT / profile.generated_directory
        self.assertTrue((directory / 'Pilot6960Entries.v').read_text().startswith(pilot_header(profile)))
        self.assertTrue((directory / 'FunctionReturnEntries.v').read_text().startswith(return_header(profile)))
        self.assertTrue((directory / 'Pilot6a38Entries.v').read_text().startswith(loop_header(profile)))

    def test_loop_head_callers_render_from_the_generic_caller(self):
        profile = load_profile()
        for head, exit_pc in [('6a24', '6a38'), ('6ac4', '6ad8')]:
            imports = [profile.qualified('Pilot' + pc + kind) for pc in (head, exit_pc)
                       for kind in ('Entries', 'Structural')]
            source = render_block_caller(profile, head, [successor_precondition(profile, head),
                                                         successor_precondition(profile, exit_pc)], imports)
            committed = ROOT / profile['callers_directory'] / ('Caller' + head + '.v')
            self.assertEqual(committed.read_text(), source)

    def test_return_precondition_matches_the_committed_caller(self):
        profile = load_profile()
        caller = (ROOT / profile['callers_directory'] / 'Caller6a78.v').read_text()
        self.assertIn('  ' + return_precondition(profile) + ' -∗\n', caller)


class OtherProfile(unittest.TestCase):
    """A second function renders without any decodeItem name."""

    def test_caller_names_only_its_own_function(self):
        profile = other_profile()
        source = render_block_caller(profile, '1000', [successor_precondition(profile, '1010'),
                                                       return_precondition(profile)],
                                     [profile.qualified('Pilot1000Entries')])
        self.assertNotRegex(source, r'(?i)decodeitem')
        self.assertIn('Require Import ZesuSsz.Generated.Other.FP301.Pilot1000Entries.\n', source)
        self.assertIn('(args : OtherArgs)', source)
        self.assertIn('  otherSelectedCode -∗\n  instr_body 0x800d1000\n', source)
        self.assertIn('instr_pre 0x800d1010 (ZesuSsz.Generated.Other.FP301.Pilot1010Entries.fp_machineAt1010', source)
        self.assertEqual(source.count('Proof.\n  zesu_block2.\nQed.\n'), 1)
        self.assertIsNone(re.search(r'\b(?:Ltac|Admitted|Axiom)\b|::=', source))

    def test_headers_and_loop_selection(self):
        profile = other_profile()
        for header in [pilot_header(profile), return_header(profile), loop_header(profile)]:
            self.assertNotRegex(header, r'(?i)decodeitem')
            self.assertIn('ZesuSsz.Contracts.OtherContract', header)
        self.assertIsNone(selected_loop_declaration('Definition fp_machineAt6a24 x.', 'header', profile))

    def test_profile_requires_every_function_value(self):
        with self.assertRaises(ValueError):
            FunctionProfile({'function': 'incomplete'})
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'other.json'
            path.write_text(json.dumps(other_profile().data))
            self.assertEqual(load_profile(str(path)).name, 'otherFunction')


if __name__ == '__main__':
    unittest.main()
