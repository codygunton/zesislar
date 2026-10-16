"""Check source-bound external call wiring without a machine proof."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from tools import test_block_table

generate_table = test_block_table.generate_table
from tools.test_generate_block_design import generator


class CallTableTests(unittest.TestCase):
    def fixture(self):
        cfg, design = test_block_table.BlockTableTests().fixture()
        f = cfg['functions'][0]
        f['rows'] = [dict(pc=0x1000, size=4, word=0x1097, kind='plain', imm=4096,
                         mnemonic='auipc', rd=1, rs1=0, rs2=0, successors=[0x1004]),
                     dict(pc=0x1004, size=4, word=0x200080e7, kind='call', imm=512,
                          mnemonic='jalr', rd=1, rs1=1, rs2=0, target=0x2200, successors=[0x1008]),
                     dict(pc=0x1008, size=4, word=0x8067, kind='return', imm=0,
                          mnemonic='jalr', rd=0, rs1=1, rs2=0, successors=[])]
        f['blocks'] = [dict(start=0x1000, end=0x1008, successors=[0x1008]),
                       dict(start=0x1008, end=0x100c, successors=[])]
        f.update(calls=[dict(pc=0x1004, target=0x2200, kind='call')], returns=[0x1008],
                 loops=[], loop_count=0, branch_count=0)
        design['blocks'] = [dict(entry_pc='0x1000', end_pc_exclusive='0x1008',
            successor_pcs=['0x1008'], incoming_edges=[dict(from_block='caller', from_instruction=None, kind='entry')]),
            dict(entry_pc='0x1008', end_pc_exclusive='0x100c', successor_pcs=[],
                 incoming_edges=[dict(from_block='0x1000', from_instruction='0x1004',
                                      kind='call', path_condition=dict(op='true'))],
                 return_clause=dict(return_instruction_pc='0x1008'))]
        design.update(block_count=2, conditional_branch_count=0, calls=[dict(
            call_site_pc='0x1004', callee_pc='0x2200', return_site_pc='0x1008',
            contract_name='Contracts.Callee.model', contract_arguments=['0x1008'],
            argument_type='CalleeArgs', outcome_type='CalleeOutcome',
            source_hashes={'Contracts/Callee.v': '0' * 64})])
        return cfg, design

    def test_call_has_external_callee_and_local_return(self):
        cfg, design = self.fixture()
        result = generate_table.structure(cfg, design)
        self.assertEqual(result['coverage']['calls'], 1)
        self.assertEqual(result['edges'], [dict(source='0x1000', instruction='0x1004',
                                              target='0x1008', condition=dict(op='true'))])
        self.assertEqual(result['calls'][0]['callee_pc'], '0x2200')
        self.assertEqual(result['calls'][0]['contract_name'], 'Contracts.Callee.model')
        self.assertNotIn('0x2200', result['missing_entry_definitions'])

    def test_inventory_cannot_choose_another_target(self):
        for owner in ('row', 'inventory', 'contract'):
            cfg, design = self.fixture()
            if owner == 'row':
                cfg['functions'][0]['rows'][1]['target'] += 4
            elif owner == 'inventory':
                cfg['functions'][0]['calls'][0]['target'] += 4
            else:
                design['calls'][0]['callee_pc'] = '0x2204'
            with self.subTest(owner=owner), self.assertRaisesRegex(ValueError, 'target|callee'):
                generate_table.structure(cfg, design)

    def test_unknown_indirect_calls_and_bad_pairs_reject(self):
        for mutation in ('prior', 'rd', 'rs1', 'funct3', 'missing', 'duplicate', 'return'):
            cfg, design = self.fixture()
            f = cfg['functions'][0]
            if mutation == 'prior': f['rows'][0]['word'] = 0x13
            elif mutation == 'rd': f['rows'][1]['word'] ^= 1 << 7
            elif mutation == 'rs1': f['rows'][1]['word'] ^= 1 << 15
            elif mutation == 'funct3': f['rows'][1]['word'] |= 1 << 12
            elif mutation == 'missing': f['calls'] = []
            elif mutation == 'duplicate': f['calls'] *= 2
            else: design['calls'][0]['return_site_pc'] = '0x100c'
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                generate_table.structure(cfg, design)

    def test_contract_is_explicit_and_exact(self):
        for mutation in ('missing', 'duplicate', 'field', 'name', 'source'):
            cfg, design = self.fixture()
            if mutation == 'missing': del design['calls']
            elif mutation == 'duplicate': design['calls'] *= 2
            elif mutation == 'field': design['calls'][0]['guess'] = True
            elif mutation == 'name': design['calls'][0]['contract_name'] = 'guessed'
            else: design['calls'][0]['source_hashes'] = {'../outside.v': '0' * 64}
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                generate_table.structure(cfg, design)

    def test_render_preserves_box_and_model_continuation(self):
        cfg, design = self.fixture()
        executable, _ = test_block_table.BlockTableTests().executable_fixture()
        design['table_convention'] = executable['table_convention']
        for block in design['blocks']:
            block.update({key: deepcopy(executable['blocks'][0][key])
                          for key in ('entry_definition', 'resource_predicate', 'binders', 'arguments', 'source_hashes')})
        result = generate_table.structure(cfg, design)
        output = generate_table.render_table(design, result, name_prefix='caller')
        self.assertIn('let model := Contracts.Callee.model (0x1008) in', output)
        self.assertIn('instr_pre 0x1008 (∃ outcome : CalleeOutcome,', output)
        self.assertIn('islarisContractAllows (CalleeArgs) (CalleeOutcome) model args outcome', output)
        self.assertIn('□ instr_pre 0x2200 callerCallState1004', output)
        self.assertNotIn('(0x2200, callerState', output)
        self.assertIn('Installation proof: pending.', output)

    def test_actual_next_uint64_pair(self):
        root = Path(__file__).resolve().parents[1]
        cfg = json.loads((root / 'build/stock-zisk/cfg.json').read_text())
        f = next(f for f in cfg['functions'] if f['name'] == 'rlp_decode.nextUint64')
        self.assertEqual(generate_table.resolved_calls(f), {0x800d62b4: 0x800d6960})

    def test_design_generator_preserves_call_kind(self):
        cfg, design = self.fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            elf = root / 'build/stock-zisk/zesu-zisk.elf'
            elf.parent.mkdir(parents=True)
            elf.write_bytes(b'fixture')
            cfg['elf_sha256'] = generate_table.digest(elf)
            source = root / 'Contracts/Callee.v'
            source.parent.mkdir()
            source.write_text('Definition model := True.\n')
            design['table_convention'] = deepcopy(test_block_table.BlockTableTests().executable_fixture()[0]['table_convention'])
            design['table_convention']['code_resource'] = 'Contracts.Callee.model'
            design['table_convention']['code_source_hashes'] = ['Contracts/Callee.v']
            for block in design['blocks']:
                block.update(entry_definition='Contracts.Callee.model', resource_predicate='Contracts.Callee.model',
                             binders=[], arguments=[], source_hashes={'Contracts/Callee.v': 'refresh'})
            profile = dict(function='fixture', design=design, hash_sources={})
            result = generator.build(cfg, 'fixture', profile, root=root)
            self.assertEqual(result['blocks'][1]['incoming_edges'][0]['kind'], 'call')
            self.assertEqual(result['calls'][0]['source_hashes']['Contracts/Callee.v'], generate_table.digest(source))


if __name__ == '__main__':
    unittest.main()
