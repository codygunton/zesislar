"""Check that the renderers read every function-specific value from a profile."""
import json
import re
from pathlib import Path
import tempfile
import unittest

from function_profiles import FunctionProfile, load_profile, loop_header, pilot_header, return_header
from join_generalize import align_join_edges, binder_names
from render_function_callers import plan_callers
from symbolic_state import input_expr
from render_fp301_statements import (
    render_block_caller,
    return_precondition,
    selected_loop_declaration,
    successor_precondition,
)

ROOT = Path(__file__).resolve().parents[2]


def other_profile():
    data = dict(load_profile('decodeItem').data)  # the resolved table, in the address form
    data.pop('symbol', None)
    data.pop('pc_base', None)
    data['pc_prefix'] = '0x800d'   # the legacy address-suffix form
    data.update({
        'function': 'otherFunction',
        'args_type': 'OtherArgs',
        'generated_directory': 'ZesuSsz/Generated/Other/FP301',
        'callers_directory': 'tools/block/generated/other_callers',
        'contract_requires': ['Require Import ZesuSsz.Contracts.OtherContract.'],
        'loop_contract_requires': ['Require Import ZesuSsz.Contracts.OtherContract.'],
        'caller_contract_requires': ['Require Import ZesuSsz.Contracts.OtherContract.'],
        'selected_code': {'module': 'ZesuSsz.Contracts.OtherSelected', 'premise': 'otherSelectedCode'},
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
        self.assertTrue((directory / 'Pilot0000Entries.v').read_text().startswith(pilot_header(profile)))
        self.assertTrue((directory / 'FunctionReturnEntries.v').read_text().startswith(return_header(profile)))
        self.assertTrue((directory / 'Pilot00d8Entries.v').read_text().startswith(loop_header(profile)))

    def test_loop_head_callers_render_from_the_generic_caller(self):
        profile = load_profile()
        for head, exit_pc in [('00c4', '00d8'), ('0164', '0178')]:
            imports = [profile.qualified('Pilot' + pc + kind) for pc in (head, exit_pc)
                       for kind in ('Entries', 'Structural')]
            source = render_block_caller(profile, head, [successor_precondition(profile, head),
                                                         successor_precondition(profile, exit_pc)], imports)
            committed = ROOT / profile['callers_directory'] / ('Caller' + head + '.v')
            self.assertEqual(committed.read_text(), source)

    def test_every_loop_head_has_a_seed_design(self):
        profile = load_profile()
        self.assertEqual([row['head'] for row in profile['loop_designs']], profile['loop_heads'])
        for row in profile['loop_designs']:
            self.assertIn(row['array_cursor']['register'], row['registers'])

    def test_return_precondition_matches_the_committed_caller(self):
        profile = load_profile()
        caller = (ROOT / profile['callers_directory'] / 'Caller0118.v').read_text()
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
        self.assertIsNone(selected_loop_declaration('Definition fp_machineAt00c4 x.', 'header', profile))

    def test_profile_requires_every_function_value(self):
        with self.assertRaises(ValueError):
            FunctionProfile({'function': 'incomplete'})
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'other.json'
            path.write_text(json.dumps(other_profile().data))
            self.assertEqual(load_profile(str(path)).name, 'otherFunction')


class CallerPlan(unittest.TestCase):
    def test_caller_plan_refuses_missing_successors(self):
        profile = other_profile()
        function = {'blocks': [{'start': 0x800d1000, 'successors': [0x800d1010]},
                               {'start': 0x800d1010, 'successors': []}]}
        cases = [{'pc': '0x800d1000', 'status': 'source_declarations_rendered'},
                 {'pc': '0x800d1010', 'status': 'source_declarations_rendered'}]
        self.assertEqual(plan_callers(profile, cases, function),
                         [('1000', ['1010'], None), ('1010', [], 'function-return package not rendered')])
        cases[1]['status'] = 'stopped'
        self.assertEqual(plan_callers(profile, cases, function)[0][2], 'successor entry not rendered: 1010')

    def test_return_block_renders_once_the_return_package_renders(self):
        profile = other_profile()
        function = {'blocks': [{'start': 0x800d1000, 'successors': [0x800d1010]},
                               {'start': 0x800d1010, 'successors': []}]}
        cases = [{'pc': '0x800d1000', 'status': 'source_declarations_rendered'},
                 {'pc': '0x800d1010', 'status': 'source_declarations_rendered'},
                 {'pc': 'function_return', 'status': 'source_declarations_rendered'}]
        self.assertEqual(plan_callers(profile, cases, function)[-1], ('1010', [], None))


class JoinEdgeAlignment(unittest.TestCase):
    ORIGINAL = {'kind': 'exists', 'binders': [{'name': 'x10', 'type': 'bv 64'}], 'scope': [],
                'body': {'kind': 'sep_list', 'children': [{'kind': 'component', 'id': 'r0'},
                                                          {'kind': 'component', 'id': 'r1'}]}}

    def edge(self, tree, terminal='K', extra=()):
        components = [{'id': 'r0', 'source': 'A'}, {'id': 'r1', 'source': terminal}, *extra]
        return {'resource_boundary': {'tree': tree, 'components': components}}

    def test_join_seed_edge_moves_onto_the_original_tree(self):
        ownership = {'tree': self.ORIGINAL, 'components': [{'id': 'r0', 'source': 'A'}, {'id': 'r1', 'source': 'True'}]}
        seeded = {'kind': 'sep', 'right': {'kind': 'component', 'id': 'r1'},
                  'left': {'kind': 'exists', 'binders': [{'name': 'machine_x12', 'type': 'bv 64', 'value_key': 'x12'}],
                           'scope': [0], 'body': {'kind': 'sep_list', 'children': [
                               {'kind': 'component', 'id': 'r0'}, {'kind': 'component', 'id': 'join_relation_0'}]}}}
        plain = self.edge(self.ORIGINAL, 'True')
        joined = self.edge(seeded, 'K', [{'id': 'join_relation_0', 'source': '⌜P⌝'}])
        aligned, extra = align_join_edges([plain, joined], ownership, 'r1', 'K')
        self.assertEqual(aligned[0], plain)
        self.assertEqual(aligned[1]['resource_boundary']['tree'], self.ORIGINAL)
        self.assertEqual([c['source'] for c in aligned[1]['resource_boundary']['components']], ['A', 'True'])
        self.assertEqual(extra, [{'name': 'machine_x12', 'type': 'bv 64'}])
        kept, _ = align_join_edges([joined], ownership, 'r1', 'K', keep_binders=True)
        self.assertEqual([b['name'] for b in kept[0]['resource_boundary']['tree']['binders']], ['x10', 'machine_x12'])

    def test_join_design_components_leave_like_relations(self):
        ownership = {'tree': self.ORIGINAL, 'components': [{'id': 'r0', 'source': 'A'}, {'id': 'r1', 'source': 'True'}]}
        seeded = {'kind': 'sep', 'right': {'kind': 'component', 'id': 'r1'},
                  'left': {'kind': 'exists', 'binders': [], 'scope': [0], 'body': {'kind': 'sep_list', 'children': [
                      {'kind': 'component', 'id': 'r0'}, {'kind': 'component', 'id': 'join_design_0'}]}}}
        joined = self.edge(seeded, 'K', [{'id': 'join_design_0', 'source': '⌜Q⌝'}])
        aligned, _ = align_join_edges([joined], ownership, 'r1', 'K')
        self.assertEqual(aligned[0]['resource_boundary']['tree'], self.ORIGINAL)
        self.assertEqual([c['source'] for c in aligned[0]['resource_boundary']['components']], ['A', 'True'])

    def test_other_differences_stay_for_the_refusal(self):
        ownership = {'tree': self.ORIGINAL, 'components': [{'id': 'r0', 'source': 'A'}, {'id': 'r1', 'source': 'True'}]}
        other = {'kind': 'sep', 'right': {'kind': 'component', 'id': 'r1'},
                 'left': {'kind': 'exists', 'binders': [], 'scope': [0],
                          'body': {'kind': 'sep_list', 'children': [{'kind': 'component', 'id': 'r9'}]}}}
        edge = self.edge(other)
        self.assertEqual(align_join_edges([edge], ownership, 'r1', 'K'), ([edge], []))


class JoinStoredBytes(unittest.TestCase):
    def test_seed_keeps_bytes_that_every_edge_holds(self):
        from types import SimpleNamespace
        from symbolic_state import MemoryRegion, bits
        import join_generalize
        source = Path(join_generalize.__file__).read_text()
        # The prefix reads an edge's own write first, then its seed's known byte.
        self.assertIn('def stored_byte(index, resource_id, offset):', source)
        self.assertLess(source.index('images[index].updates[resource_id].get(offset)'),
                        source.index('for region in states[index].memory:'))


class JoinBinderNames(unittest.TestCase):
    def test_names_stay_unless_an_upstream_binder_collides(self):
        paths = [{'x12': input_expr('a', 64)}, {'x12': input_expr('b', 64)}]
        self.assertEqual(binder_names(paths, ['x12']), {'x12': 'machine_x12'})
        paths = [{'x12': input_expr('machine_x12', 64)}, {'x12': input_expr('b', 64)}]
        self.assertEqual(binder_names(paths, ['x12']), {'x12': 'machine_x12_1'})
        self.assertEqual(binder_names(paths[1:], ['x12'], ['machine_x12']), {'x12': 'machine_x12_1'})


if __name__ == '__main__':
    unittest.main()
