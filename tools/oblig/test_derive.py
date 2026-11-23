"""derive.py: CFG requests of round 1 and the requests of recorded render refusals."""
from pathlib import Path
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import derive  # noqa: E402

BASE = 0x1000
CALLEE = 0x2000


def row(pc, kind, mnemonic, rd=0, rs1=0, rs2=0, **extra):
    return {'pc': pc, 'kind': kind, 'mnemonic': mnemonic, 'rd': rd, 'rs1': rs1, 'rs2': rs2, 'imm': 0, **extra}


# 1000: branch to 1008 or 1010; 1008 falls into the join 1010; 1010 calls CALLEE at 1014;
# 1018 loops back to 1010 or returns at 101c.
FUNCTION = {
    'name': 'demo.fn', 'entry': BASE, 'end': BASE + 0x20,
    'rows': [row(0x1000, 'store', 'sd', rs1=2, rs2=1, width=8, address_analysis=['stack', -8]),
             row(0x1004, 'branch', 'beq', rs1=10, rs2=0),
             row(0x1008, 'plain', 'addi', rd=10, rs1=10),
             row(0x100c, 'plain', 'addi', rd=11, rs1=10),
             row(0x1010, 'plain', 'addi', rd=10, rs1=12),
             row(0x1014, 'call', 'jalr', rd=1, rs1=1),
             row(0x1018, 'branch', 'bne', rs1=10, rs2=0),
             row(0x101c, 'return', 'jalr', rs1=1)],
    'blocks': [{'start': 0x1000, 'end': 0x1008, 'successors': [0x1008, 0x1010]},
               {'start': 0x1008, 'end': 0x1010, 'successors': [0x1010]},
               {'start': 0x1010, 'end': 0x1018, 'successors': [0x1018]},
               {'start': 0x1018, 'end': 0x101c, 'successors': [0x1010, 0x101c]},
               {'start': 0x101c, 'end': 0x1020, 'successors': []}],
    'calls': [{'pc': 0x1014, 'target': CALLEE, 'kind': 'call'}],
    'returns': [0x101c],
    'loops': [{'minimum_pc': hex(0x1010), 'backward_edges': [{'from': hex(0x1018), 'to': hex(0x1010)}]}]}

# A second shape without the loop: 1010 is then a join, not a cut.
JOIN_FUNCTION = dict(FUNCTION, loops=[], blocks=[
    *FUNCTION['blocks'][:3], {'start': 0x1018, 'end': 0x101c, 'successors': [0x101c]}, FUNCTION['blocks'][4]])


class Derive(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / 'registry.json').write_text(json.dumps({'functions': []}))

    def run_derive(self, function, render=None, **options):
        (self.root / 'cfg.json').write_text(json.dumps({'functions': [function]}))
        options.setdefault('inventory', self.root / 'no-inventory.json')
        return derive.derive('demo', self.root / 'run', symbol='demo.fn', cfg=self.root / 'cfg.json',
                             render=render, registry_path=self.root / 'registry.json',
                             names={CALLEE: 'callee.fn'}, **options)

    def registry(self, status):
        (self.root / 'registry.json').write_text(json.dumps({'functions': [{
            'function': 'callee', 'symbol': 'callee.fn', 'status': status,
            'interface': {'module': 'Demo.Interface'}, 'call_spec': {'name': 'calleeSpec'}}]}))

    def test_a_call_to_a_proved_callee_gets_the_callee_side_of_its_row(self):
        """The callee side is what every other caller's profile row agrees on; caller terms stay open."""
        self.registry('proved')
        profiles = self.root / 'functions'
        profiles.mkdir()
        def call(site, caller_value):
            return {'function': 'other.fn', 'call_site_pc': site, 'callee_pc': 'callee.fn+0x0',
                    'spec': 'calleeSpec', 'spec_module': 'Demo.Interface', 'spec_source': 'Demo/Interface.v',
                    'stack_bytes': 16, 'output_length_source': 'fixture',
                    'arrays': [{'binder': 'input', 'argument': 1, 'caller_value': caller_value},
                               {'binder': 'out', 'argument': 0, 'length': 40, 'length_source': 'fixture'}]}
        (profiles / 'other.json').write_text(json.dumps({'calls': [call('+0x10', 'a'), call('+0x20', 'b')]}))
        (profiles / 'other.annotations.json').write_text(json.dumps({'calls': [call('+0x30', 'c')]}))
        result = self.run_derive(FUNCTION, profiles=profiles)
        row, = [row for row in result['requests'] if row['kind'] == 'call_row']
        self.assertTrue(row['derivable'])
        self.assertEqual(row['proposal']['at'], {'pc': '+0x14', 'boundary': 'call_site'})
        self.assertEqual(row['proposal']['call'], {
            'function': 'demo.fn', 'callee_pc': 'callee.fn+0x0', 'return_site_pc': '+0x18', 'spec': 'calleeSpec',
            'spec_module': 'Demo.Interface', 'spec_source': 'Demo/Interface.v', 'stack_bytes': 16,
            'output_length_source': 'fixture',
            'arrays': [{'binder': 'input', 'argument': 1},
                       {'binder': 'out', 'argument': 0, 'length': 40, 'length_source': 'fixture'}]})
        self.assertEqual(row['proposal']['open'], ['arrays[input].caller_value'])
        self.assertNotIn('callee_premise', {row['kind'] for row in result['requests']})
        # A callee without a registry row, or one with another status, gets no proposal.
        for status in ('candidate', None):
            if status is None:
                (self.root / 'registry.json').write_text(json.dumps({'functions': []}))
            else:
                self.registry(status)
            row, = [row for row in self.run_derive(FUNCTION, profiles=profiles)['requests']
                    if row['kind'] == 'call_row']
            self.assertEqual((row['derivable'], row['proposal']), (False, None))

    def test_without_other_callers_the_spec_gives_the_callee_side(self):
        """The committed decodeItem interface spec: binders, arguments and stack; lengths stay open."""
        entry = next(row for row in json.loads(derive.REGISTRY.read_text())['functions']
                     if row['function'] == 'decodeItem')
        fields, arrays, open_fields = derive.spec_call_fields(entry)
        self.assertEqual(fields['spec'], entry['call_spec']['name'])
        self.assertEqual(fields['spec_source'], 'ZesuSsz/Interfaces/DecodeItem.v')
        self.assertEqual([(row['binder'], row['argument']) for row in arrays], [('input', 1), ('before', 0)])
        self.assertIn('output_length_source', open_fields)

    def dispatch_function(self, write_index=False):
        """1000 masks a2 and jumps through a 3-entry table at 1004 to 1008, 100c or 1010."""
        rows = [row(0x1000, 'plain', 'andi', rd=10, rs1=12),
                row(0x1004, 'indirect', 'jalr', rs1=10, resolution='three checked table entries',
                    successors=[0x1008, 0x100c, 0x1010]),
                *[row(pc, 'return', 'jalr', rs1=1) for pc in (0x1008, 0x100c, 0x1010)]]
        if write_index:
            rows[0] = row(0x1000, 'plain', 'addi', rd=12, rs1=12)
            rows.insert(1, row(0x1002, 'plain', 'andi', rd=10, rs1=12))
        blocks = [{'start': 0x1000, 'end': 0x1008, 'successors': [0x1008, 0x100c, 0x1010]},
                  *[{'start': pc, 'end': pc + 4, 'successors': []} for pc in (0x1008, 0x100c, 0x1010)]]
        function = {'name': 'demo.fn', 'entry': BASE, 'end': BASE + 0x14, 'rows': rows, 'blocks': blocks,
                    'calls': [], 'returns': [0x1008, 0x100c, 0x1010], 'loops': []}
        # The table address is data: built here, named by the symbol table.
        table = BASE + 0x400
        (self.root / 'inventory.json').write_text(json.dumps({'functions': [{'name': 'demo.fn', 'dispatch': {
            'pc': 0x1004, 'table_address': table, 'index_register': 12, 'index_mask': 255,
            'index_bounds': [0, 2], 'bound_status': 'Required entry condition.',
            'targets': [0x1008, 0x100c, 0x1010],
            'evidence_instructions': [0x1002 if write_index else 0x1000, 0x1004]}}]}))
        return function

    def test_a_jump_table_is_a_predicate_request_with_its_index_bound(self):
        result = self.run_derive(self.dispatch_function(), inventory=self.root / 'inventory.json')
        row, = [row for row in result['requests'] if row['kind'] == 'predicate']
        self.assertEqual((row['id'], row['pc'], row['derivable']), ('demo/decision/predicate-0004', '+0x4', True))
        self.assertIn('3 entries', row['needs'][0])
        self.assertIn('index x12 & 255 in [0, 2]', row['needs'][1])
        self.assertEqual(row['proposal']['facts'], [{'coq': '(0 <= Z.land (bv_unsigned entry_x12) 255 <= 2)%Z',
                                                     'role': 'dispatch_bound'}])
        self.assertEqual(row['proposal']['binders'], [{'name': 'entry_x12', 'register': 'x12'}])
        # An index written before the jump is no entry value: the request stays, without a proposal.
        function = self.dispatch_function(write_index=True)
        result = self.run_derive(function, inventory=self.root / 'inventory.json')
        row, = [row for row in result['requests'] if row['kind'] == 'predicate']
        self.assertFalse(row['derivable'])
        self.assertIn('not an entry fact', row['needs'][-1])
        # Without the closure record the jump still surfaces, with its entry count only.
        row, = [row for row in self.run_derive(function)['requests'] if row['kind'] == 'predicate']
        self.assertEqual((row['derivable'], len(row['needs'])), (False, 1))

    def render_dir(self, cases, forward=None):
        render = self.root / 'render'
        (render / 'render').mkdir(parents=True)
        (render / 'render/RESULT.json').write_text(json.dumps({'cases': cases}))
        if forward is not None:
            (render / 'forward').mkdir()
            (render / 'forward/FORWARD.json').write_text(json.dumps(forward))
        return render

    def test_round_one_issues_the_cfg_requests(self):
        result = self.run_derive(FUNCTION)
        self.assertEqual(result['round'], 1)
        self.assertEqual({key: value for key, value in result['counts'].items() if value},
                         {'contract': 1, 'loop_assertion': 1, 'call_row': 1, 'callee_premise': 1})
        ids = {row['id'] for row in result['requests']}
        self.assertEqual(ids, {'demo/decision/contract-0000', 'demo/decision/loop_assertion-0010',
                               'demo/decision/call_row-0014', 'demo/decision/callee_premise-0014'})
        derived = self.root / 'run/round-1/derived'
        for name in ('LIVE.json', 'FRAME.json', 'JOIN-STATEMENTS.json', 'CALLEES.json', 'CONTRACT-SKELETON.v',
                     'REQUESTS.json'):
            self.assertTrue((derived / name).exists(), name)
        frame = json.loads((derived / 'FRAME.json').read_text())
        self.assertEqual(frame['slots'], [{'offset': -8, 'size': 8, 'reads': [], 'writes': ['+0x0'],
                                           'first_writer': '+0x0'}])
        callees = json.loads((derived / 'CALLEES.json').read_text())['calls']
        self.assertEqual([(row['call_site'], row['callee'], row['status']) for row in callees],
                         [('+0x14', 'callee.fn', None)])
        # The next call writes the next round.
        self.assertEqual(self.run_derive(FUNCTION)['round'], 2)

    def test_a_refused_incomplete_join_boundary_is_a_join_assertion_request(self):
        render = self.render_dir([{'pc': hex(0x1010), 'status': 'refused_incomplete_boundary', 'proof_ran': False,
                                   'reports': [{'kind': 'reaching_stop_guard', 'detail':
                                                '2 retained stops can reach the boundary 0x1010; the first is '
                                                'state_check in block 0x1008 at 0x100c.'}]}])
        result = self.run_derive(JOIN_FUNCTION, render)
        joins = [row for row in result['requests'] if row['kind'] == 'join_assertion']
        self.assertEqual(len(joins), 1)
        self.assertEqual((joins[0]['id'], joins[0]['pc'], joins[0]['derivable']),
                         ('demo/decision/join_assertion-0010', '+0x10', False))
        self.assertIn('incomplete join boundary', joins[0]['reason'])
        self.assertEqual(joins[0]['sources'], ['render/RESULT.json#0x1010'])

    def test_an_exact_join_statement_is_a_derivable_proposal(self):
        def alternative(predecessor, value):
            return {'predecessor_pc': hex(predecessor), 'seed_pc': hex(BASE), 'path': [0],
                    'state': {'registers': {'x10': {'op': 'bits', 'width': 64, 'value': value}}, 'conditions': []}}
        forward = {'stops': [], 'liveness': {hex(0x1010): ['x10']},
                   'boundaries': [{'pc': hex(0x1010), 'status': 'handwritten_cut', 'reaching_stops': [],
                                   'alternatives': [alternative(0x1000, 1), alternative(0x1008, 2)]}]}
        render = self.render_dir([{'pc': hex(0x1010), 'status': 'refused_mixed_roots', 'roots': ['a', 'b'],
                                   'proof_ran': False}], forward)
        result = self.run_derive(JOIN_FUNCTION, render)
        join, = [row for row in result['requests'] if row['kind'] == 'join_assertion']
        self.assertTrue(join['derivable'])
        self.assertEqual(join['proposal']['facts'], [{'coq': '((machine_x10 = (BV 64%N 1%Z))) \\/ '
                                                             '((machine_x10 = (BV 64%N 2%Z)))', 'role': 'fact'}])
        self.assertEqual(join['proposal']['at'], {'pc': '+0x10', 'boundary': 'join'})

    def test_a_refusal_no_annotation_answers_is_reported_not_requested(self):
        render = self.render_dir([{'pc': hex(0x1008), 'status': 'refused_no_alternatives', 'proof_ran': False,
                                   'reports': [{'kind': 'unreached_boundary', 'detail': 'no alternative'}]}])
        result = self.run_derive(JOIN_FUNCTION, render)
        self.assertEqual([row['reason'] for row in result['refusals_without_request']], ['refused_no_alternatives'])

    def test_tx_access_list_round_one_floor(self):
        """The committed CFG: 1 contract, 3 loop cuts, 12 call rows, 7 callees without a registry row; the
        5 decodeItem call rows take their callee side from the decodeParentHeader and nextUint64 profiles."""
        with tempfile.TemporaryDirectory() as run:
            result = derive.derive('txAccessList', Path(run), symbol='rlp_decode.txAccessList')
        counts = {key: value for key, value in result['counts'].items() if value}
        self.assertEqual(counts, {'contract': 1, 'loop_assertion': 3, 'call_row': 12, 'callee_premise': 7})
        loops = {row['pc']: row['needs'] for row in result['requests'] if row['kind'] == 'loop_assertion'}
        self.assertEqual(sorted(loops), ['+0x18c', '+0x2ec', '+0xc4'])
        self.assertTrue(loops['+0x2ec'][0].startswith('hand loop_heads row'))
        self.assertEqual(loops['+0xc4'], [])
        derivable = sorted(row['pc'] for row in result['requests'] if row['derivable'])
        self.assertEqual(derivable, ['+0x108', '+0x158', '+0x19c', '+0x64', '+0xd4'])

    def test_decode_tx_fields_jump_table_and_non_natural_heads(self):
        with tempfile.TemporaryDirectory() as run:
            result = derive.derive('decodeTxFields', Path(run), symbol='rlp_decode.decodeTxFields')
        predicate, = [row for row in result['requests'] if row['kind'] == 'predicate']
        self.assertEqual((predicate['pc'], predicate['derivable']), ('+0x78', True))
        self.assertIn('5 entries', predicate['needs'][0])
        hand = sorted(row['pc'] for row in result['requests'] if row['kind'] == 'loop_assertion'
                      and row['needs'] and row['needs'][0].startswith('hand loop_heads row'))
        self.assertEqual(hand, ['+0x1f10', '+0x1f14'])
        self.assertEqual(sum(row['derivable'] for row in result['requests'] if row['kind'] == 'call_row'), 63)


if __name__ == '__main__':
    unittest.main()
