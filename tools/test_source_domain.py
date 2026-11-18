"""Source projection and RAM-fault refusal controls use no proof captures."""
from copy import deepcopy
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from source_domain import constant_from_source, project_layout_domain
from symbolic_state import (SymbolicState, _refuted_ram_guard, bits,
                            evaluate_trace, input_expr, operation)


class DomainTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.contract = self.root / 'Contract.v'
        self.layout = self.root / 'Layout.v'
        source = Path(__file__).resolve().parents[1] / 'ZesuSsz/Contracts'
        self.contract.write_bytes((source / 'RlpDecodeItemContract.v').read_bytes())
        self.layout.write_bytes((source / 'RlpDecodeItem.v').read_bytes())
        self.map = self.root / 'Map.v'
        self.map.write_text('Definition defaultMap := {| mapRamBase := 4096; mapRamSize := 4096 |}.\n'
                            'Definition machineRamEnd (machine : MachineMap) : Z := '
                            '(mapRamBase machine + mapRamSize machine)%Z.\n')
        self.arguments = {'inputPointer': 'decodeItemInputPointer args',
                          'inputLength': 'decodeItemInputLength args',
                          'resultPointer': 'decodeItemOutputPointer args',
                          'stackPointer': 'decodeItemStackPointer args',
                          'returnAddress': 'decodeItemReturnAddress args',
                          'inputEnd': 'decodeItemInputEnd args'}

    def binding(self, path, declaration, **fields):
        return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'declaration': declaration, **fields}

    def parameters(self):
        record = self.binding(self.map, 'defaultMap')
        constants = {
            'decodeItemStackBytes': constant_from_source(self.binding(self.layout, 'decodeItemStackBytes')),
            'word64Modulus': constant_from_source(self.binding(self.layout, 'word64Modulus')),
            'mapRamBase defaultMap': constant_from_source({**record, 'field': 'mapRamBase'}),
            'machineRamEnd defaultMap': constant_from_source(self.binding(
                self.map, 'machineRamEnd', sum_fields=['mapRamBase', 'mapRamSize'],
                parameter='machine', record_source=record))}
        return dict(layout_source=self.binding(self.layout, 'decodeItemEntryLayout'),
                    wellformed_source=self.binding(self.contract, 'decodeItemArgsWellFormed'),
                    arguments=self.arguments,
                    resource_roles={'input': 'input', 'output': 'output', 'stack': 'stack'},
                    source_constants=constants,
                    interval_layout={'stack': 'stackPointer', 'frame_size': 'decodeItemStackBytes',
                                     'modulus': 'word64Modulus', 'ram_base': 'mapRamBase defaultMap',
                                     'ram_end': 'machineRamEnd defaultMap'})

    def test_exact_domain_projection_preserves_source_and_adds_no_premise(self):
        original = self.contract.read_bytes(), self.layout.read_bytes()
        result = project_layout_domain(**self.parameters())
        self.assertEqual(result['premises_added'], [])
        self.assertFalse(result['entry_assertion_changed'])
        self.assertEqual([r['kind'] for r in result['facts']].count('disjoint_ranges'), 3)
        interval = result['facts'][-1]['terms']['unsigned_interval']
        self.assertEqual((interval['minimum'], interval['maximum']), (4112, 8192))
        self.assertEqual(original, (self.contract.read_bytes(), self.layout.read_bytes()))

    def test_missing_ram_bound_refuses(self):
        self.layout.write_text(self.layout.read_text().replace(
            '  stackPointer <= machineRamEnd defaultMap /\\\n', ''))
        with self.assertRaisesRegex(ValueError, 'bound is absent'):
            project_layout_domain(**self.parameters())

    def test_layout_not_in_domain_refuses(self):
        self.contract.write_text(self.contract.read_text().replace(
            '  decodeItemEntryLayout\n', '  unrelatedLayout\n', 1))
        with self.assertRaisesRegex(ValueError, 'exact layout application'):
            project_layout_domain(**self.parameters())

    def test_changed_source_hash_refuses(self):
        values = self.parameters()
        self.layout.write_text(self.layout.read_text() + '\n')
        with self.assertRaisesRegex(ValueError, 'hash differs'):
            project_layout_domain(**values)

    def test_changed_constant_value_refuses(self):
        values = self.parameters()
        values['source_constants']['decodeItemStackBytes']['value'] = 8
        with self.assertRaisesRegex(ValueError, 'differs from its source'):
            project_layout_domain(**values)

    def test_aliased_ownership_ids_refuse(self):
        values = self.parameters()
        values['resource_roles']['stack'] = 'input'
        with self.assertRaisesRegex(ValueError, 'distinct existing ownership'):
            project_layout_domain(**values)

    def test_changed_separation_application_refuses(self):
        self.layout.write_text(self.layout.read_text().replace(
            'separateRanges inputPointer inputLength resultPointer 40',
            'separateRanges resultPointer inputLength inputPointer 40'))
        with self.assertRaisesRegex(ValueError, 'ownership roles'):
            project_layout_domain(**self.parameters())


class FaultTests(unittest.TestCase):
    def setUp(self):
        self.pointer = input_expr('sp', 64)
        self.rows = [{'expression': self.pointer.to_dict(), 'minimum': 4112, 'maximum': 8192,
                      'ram_base': 4096, 'ram_end': 8192, 'origin': {'source': 'fixture'}}]
        self.address = operation('bvadd', operation('bvadd', self.pointer, bits(-16, 64)), bits(8, 64))

    def guard(self, end=False):
        address = operation('zero_extend', self.address, width=128)
        if end:
            address = operation('bvadd', address, bits(8, 128))
        return operation('not', operation('bvsle' if end else 'bvsge', address,
                                          bits(8192 if end else 4096, 128)))

    def test_both_ram_fault_guards_refute_with_existing_bounds(self):
        self.assertIsNotNone(_refuted_ram_guard(self.guard(), self.rows))
        self.assertIsNotNone(_refuted_ram_guard(self.guard(True), self.rows))

    def test_missing_bounds_refuse(self):
        self.assertIsNone(_refuted_ram_guard(self.guard(), []))

    def test_unknown_or_unsupported_address_refuses(self):
        self.address = operation('bvand', self.pointer, bits(255, 64))
        self.assertIsNone(_refuted_ram_guard(self.guard(), self.rows))

    def test_modular_wrap_ambiguity_refuses(self):
        rows = deepcopy(self.rows)
        rows[0]['minimum'] = 0
        self.assertIsNone(_refuted_ram_guard(self.guard(), rows))

    def test_ambiguous_interval_refuses(self):
        self.assertIsNone(_refuted_ram_guard(self.guard(), self.rows + self.rows))

    def test_missing_origin_refuses(self):
        rows = deepcopy(self.rows)
        rows[0].pop('origin')
        self.assertIsNone(_refuted_ram_guard(self.guard(), rows))

    def test_unrelated_endpoint_refuses(self):
        condition = operation('not', operation('bvsge', self.pointer, bits(7, 64)))
        self.assertIsNone(_refuted_ram_guard(condition, self.rows))

    def test_trace_prunes_only_exception_leaf_and_retains_obligation(self):
        state = SymbolicState(registers={'x2': self.pointer}, source_intervals=self.rows)
        trace = '''(trace
          (declare-const p (_ BitVec 64)) (read-reg |x2| nil p)
          (define-const address (bvadd p #xfffffffffffffff8))
          (assert (not (bvsge ((_ zero_extend 64) address) #x00000000000000000000000000001000)))
          (write-reg |mcause| nil #x0000000000000007)
          (write-reg |mepc| nil #x0000000000000000)
          (write-reg |mtval| nil address)
          (write-reg |cur_privilege| nil |Machine|)
          (write-reg |PC| nil #x0000000000000000))'''
        result = evaluate_trace(trace, state)[0]
        self.assertEqual(result.status, 'infeasible')
        report = result.state.reports[-1]
        self.assertEqual(report['kind'], 'source_ram_fault_refutation')
        self.assertEqual(report['proof_status'], 'open')
        self.assertTrue(report['required_rocq_guard_projection'])
        self.assertEqual(report['proof_premises_added'], [])
        ordinary = trace.replace('(write-reg |mcause| nil #x0000000000000007)', '')
        self.assertEqual(evaluate_trace(ordinary, state)[0].status, 'complete')

    def test_copy_preserves_bounds_without_changing_original(self):
        state = SymbolicState(source_intervals=self.rows)
        copy = state.copy()
        copy.source_intervals.clear()
        self.assertEqual(len(state.source_intervals), 1)


if __name__ == '__main__':
    unittest.main()
