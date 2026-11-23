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

    def run_derive(self, function, render=None):
        (self.root / 'cfg.json').write_text(json.dumps({'functions': [function]}))
        return derive.derive('demo', self.root / 'run', symbol='demo.fn', cfg=self.root / 'cfg.json',
                             render=render, registry_path=self.root / 'registry.json',
                             names={CALLEE: 'callee.fn'})

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
        """The committed CFG: 1 contract, 3 loop cuts, 12 call rows, 7 callees without a registry row."""
        with tempfile.TemporaryDirectory() as run:
            result = derive.derive('txAccessList', Path(run), symbol='rlp_decode.txAccessList')
        counts = {key: value for key, value in result['counts'].items() if value}
        self.assertEqual(counts, {'contract': 1, 'loop_assertion': 3, 'call_row': 12, 'callee_premise': 7})
        loops = sorted(row['pc'] for row in result['requests'] if row['kind'] == 'loop_assertion')
        self.assertEqual(loops, ['+0x18c', '+0x2ec', '+0xc4'])


if __name__ == '__main__':
    unittest.main()
