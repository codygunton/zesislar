"""Source projection and RAM-fault refusal controls use no proof captures."""
from copy import deepcopy
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from source_domain import constant_from_source, project_layout_domain
from symbolic_state import (Expr, SymbolicState, _implied_ram_guard, _refuted_ram_guard, bits,
                            _source_comparison_refutation, evaluate_trace, input_expr, operation)


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

    def projection_parameters(self, *, output='resultPointer', extent='40', returned='returnAddress',
                              period='4', residue='0'):
        values = self.parameters()
        values['layout_projections'] = {'source': values['layout_source'],
            'output': {'pointer': output, 'extent': extent},
            'return': {'pointer': returned, 'modulus': period, 'residue': residue}}
        return values

    def test_exact_domain_projection_preserves_source_and_adds_no_premise(self):
        original = self.contract.read_bytes(), self.layout.read_bytes()
        result = project_layout_domain(**self.parameters())
        self.assertEqual(result['premises_added'], [])
        self.assertFalse(result['entry_assertion_changed'])
        self.assertEqual([r['kind'] for r in result['facts']].count('disjoint_ranges'), 3)
        interval = result['facts'][-1]['terms']['unsigned_interval']
        self.assertEqual((interval['minimum'], interval['maximum']), (4112, 8192))
        self.assertEqual(len(result['facts']), 5)
        self.assertFalse(any(fact['kind'] == 'alignment' for fact in result['facts']))
        self.assertEqual(original, (self.contract.read_bytes(), self.layout.read_bytes()))

    def test_existing_output_bounds_project_the_complete_array_interval(self):
        result = project_layout_domain(**self.projection_parameters())
        interval = next(fact['terms']['unsigned_interval'] for fact in result['facts']
                        if fact['fact_id'] == 'layout:output-interval')
        self.assertEqual((interval['minimum'], interval['maximum']), (4096, 8192 - 40))
        self.assertEqual(interval['expression'], input_expr('(Z_to_bv 64%N (decodeItemOutputPointer args))').to_dict())
        fact = next(fact for fact in result['facts'] if fact['fact_id'] == 'layout:output-interval')
        self.assertEqual(len(fact['origin']['source_clauses']), 4)
        self.assertEqual(result['premises_added'], [])

    def test_missing_output_end_bound_refuses(self):
        self.layout.write_text(self.layout.read_text().replace(
            '  resultPointer + 40 <= machineRamEnd defaultMap /\\\n', ''))
        with self.assertRaisesRegex(ValueError, 'source output/RAM bound is absent'):
            project_layout_domain(**self.projection_parameters())

    def test_output_store_ram_guards_use_the_projected_source_interval(self):
        result = project_layout_domain(**self.projection_parameters())
        fact = next(fact for fact in result['facts'] if fact['fact_id'] == 'layout:output-interval')
        interval = {**fact['terms']['unsigned_interval'], 'origin': fact['origin']}
        pointer = Expr.from_dict(interval['expression'])
        address = operation('zero_extend', operation('bvadd', pointer, bits(32, 64)), width=128)
        end = operation('bvadd', address, bits(8, 128))
        guard = operation('not', operation('bvsle', end, bits(8192, 128)))
        self.assertIsNotNone(_refuted_ram_guard(guard, [interval]))

    def test_output_access_beyond_the_array_does_not_get_refuted(self):
        result = project_layout_domain(**self.projection_parameters())
        fact = next(fact for fact in result['facts'] if fact['fact_id'] == 'layout:output-interval')
        interval = {**fact['terms']['unsigned_interval'], 'origin': fact['origin']}
        pointer = Expr.from_dict(interval['expression'])
        address = operation('zero_extend', operation('bvadd', pointer, bits(40, 64)), width=128)
        end = operation('bvadd', address, bits(8, 128))
        guard = operation('not', operation('bvsle', end, bits(8192, 128)))
        self.assertIsNone(_refuted_ram_guard(guard, [interval]))

    def test_projection_uses_renamed_source_parameters(self):
        self.layout.write_text(self.layout.read_text().replace('resultPointer', 'destination')
                               .replace('returnAddress', 'returnPc'))
        self.arguments['destination'] = self.arguments.pop('resultPointer')
        self.arguments['returnPc'] = self.arguments.pop('returnAddress')
        result = project_layout_domain(**self.projection_parameters(output='destination', returned='returnPc'))
        projected = {fact['fact_id']: fact for fact in result['facts']}
        self.assertIn('decodeItemOutputPointer', str(projected['layout:output-interval']['terms']))
        self.assertIn('decodeItemReturnAddress', str(projected['layout:return-alignment']['terms']))

    def test_projection_uses_a_different_source_extent_and_congruence(self):
        self.layout.write_text(self.layout.read_text().replace('resultPointer + 40', 'resultPointer + 48')
                               .replace('resultPointer 40', 'resultPointer 48')
                               .replace('returnAddress mod 4 = 0', 'returnAddress mod 8 = 2'))
        result = project_layout_domain(**self.projection_parameters(extent='48', period='8', residue='2'))
        projected = {fact['fact_id']: fact for fact in result['facts']}
        self.assertEqual(projected['layout:output-interval']['terms']['unsigned_interval']['maximum'], 8192 - 48)
        self.assertEqual(projected['layout:return-alignment']['terms']['alignment']['modulus'], 8)
        self.assertEqual(projected['layout:return-alignment']['terms']['alignment']['residue'], 2)

    def test_ambiguous_output_clause_refuses(self):
        self.layout.write_text(self.layout.read_text().replace('  mapRamBase defaultMap <= resultPointer /\\',
            '  mapRamBase defaultMap <= resultPointer /\\ mapRamBase defaultMap <= resultPointer /\\'))
        with self.assertRaisesRegex(ValueError, 'source output/RAM bound is absent or ambiguous'):
            project_layout_domain(**self.projection_parameters())

    def test_absent_return_clause_refuses(self):
        self.layout.write_text(self.layout.read_text().replace(' /\\ returnAddress mod 4 = 0', ''))
        with self.assertRaisesRegex(ValueError, 'source return alignment is absent or ambiguous'):
            project_layout_domain(**self.projection_parameters())

    def test_ambiguous_return_clause_refuses(self):
        self.layout.write_text(self.layout.read_text().replace('returnAddress mod 4 = 0',
            'returnAddress mod 4 = 0 /\\ returnAddress mod 4 = 0'))
        with self.assertRaisesRegex(ValueError, 'source return alignment is absent or ambiguous'):
            project_layout_domain(**self.projection_parameters())

    def test_projection_cannot_use_another_source_binding(self):
        values = self.projection_parameters()
        values['layout_projections']['source'] = {**values['layout_source'], 'sha256': 'different'}
        with self.assertRaisesRegex(ValueError, 'exact source binding'):
            project_layout_domain(**values)

    def test_named_projection_constants_retain_their_exact_origins(self):
        source = self.layout.read_text().replace('resultPointer + 40', 'resultPointer + resultExtent')
        source = source.replace('resultPointer 40', 'resultPointer resultExtent')
        source = source.replace('returnAddress mod 4 = 0', 'returnAddress mod returnPeriod = returnResidue')
        source = source.replace('Definition decodeItemEntryLayout',
            'Definition resultExtent : Z := 48.\nDefinition returnPeriod : Z := 8.\n'
            'Definition returnResidue : Z := 2.\nDefinition decodeItemEntryLayout')
        self.layout.write_text(source)
        values = self.projection_parameters(extent='resultExtent', period='returnPeriod', residue='returnResidue')
        constants = {name: constant_from_source(self.binding(self.layout, name))
                     for name in ('resultExtent', 'returnPeriod', 'returnResidue')}
        values['source_constants'].update(constants)
        result = project_layout_domain(**values)
        facts = {fact['fact_id']: fact for fact in result['facts']}
        self.assertEqual(facts['layout:output-interval']['origin']['constants']['resultExtent'], constants['resultExtent'])
        for name in ('returnPeriod', 'returnResidue'):
            self.assertEqual(facts['layout:return-alignment']['origin']['constants'][name], constants[name])

    def test_projection_refuses_a_pointer_absent_from_the_source(self):
        with self.assertRaisesRegex(ValueError, 'not a source parameter'):
            project_layout_domain(**self.projection_parameters(output='missingPointer'))

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

    def test_literal_definitions_and_parsing_notations_have_equal_values(self):
        path = self.root / 'Constant.v'
        for kind, expression in [('Z', '2 ^ 64'), ('N', '40%N'), ('nat', '8 + 8 * 2')]:
            with self.subTest(kind=kind):
                path.write_text(f'Definition constant : {kind} := {expression}.\n')
                old = constant_from_source(self.binding(path, 'constant'))
                path.write_text(f'Notation constant := (({expression}) : {kind}) (only parsing).\n')
                binding = self.binding(path, 'constant')
                new = constant_from_source(binding)
                self.assertEqual((old['value'], old['type']), (new['value'], new['type']))
                self.assertEqual(new['origin'], binding)

    def test_numeric_notation_rejects_symbolic_or_unbounded_expressions(self):
        path = self.root / 'Constant.v'
        for expression in ['symbol + 1', '2 ^ 129', '2 ^ 128 * 2 ^ 128 * 2',
                           '__import__("os")', '(40 : bool)']:
            with self.subTest(expression=expression):
                path.write_text(f'Notation constant := ({expression}) (only parsing).\n')
                with self.assertRaises(ValueError):
                    constant_from_source(self.binding(path, 'constant'))

    def test_numeric_notation_requires_unique_parsing_only_declaration(self):
        path = self.root / 'Constant.v'
        for source in ['Notation constant := (40 : Z).\n',
                       'Notation constant := (40 : Z) (only parsing).\n'
                       'Definition constant : Z := 40.\n']:
            path.write_text(source)
            with self.assertRaises(ValueError):
                constant_from_source(self.binding(path, 'constant'))

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

    def test_source_contradiction_prunes_each_leaf_and_retains_its_obligation(self):
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
        ordinary_result, = evaluate_trace(ordinary, state)
        self.assertEqual(ordinary_result.status, 'infeasible')
        self.assertEqual(ordinary_result.state.reports[-1]['rule'], 'source_interval_comparison')
        self.assertTrue(ordinary_result.state.reports[-1]['required_rocq_guard_projection'])
        self.assertEqual(ordinary_result.state.reports[-1]['proof_premises_added'], [])

    def test_source_implied_ram_guards_hold_and_are_not_refuted(self):
        for end in (False, True):
            holding = self.guard(end).args[0]
            self.assertIsNotNone(_implied_ram_guard(holding, self.rows))
            self.assertIsNone(_refuted_ram_guard(holding, self.rows))
            self.assertIsNone(_implied_ram_guard(self.guard(end), self.rows))
            self.assertIsNone(_implied_ram_guard(holding, []))

    def test_source_implied_ram_guard_is_not_carried(self):
        state = SymbolicState(registers={'x2': self.pointer}, source_intervals=self.rows)
        trace = '''(trace
          (declare-const p (_ BitVec 64)) (read-reg |x2| nil p)
          (define-const address (bvadd p #xfffffffffffffff8))
          (assert (bvsge ((_ zero_extend 64) address) #x00000000000000000000000000001000))
          (assert (bvsle (bvadd ((_ zero_extend 64) address) #x00000000000000000000000000000008)
                         #x00000000000000000000000000002000))
          (assert (bvsge address #x0000000000001100)))'''
        result, = evaluate_trace(trace, state)
        self.assertEqual(result.status, 'complete')
        self.assertEqual([condition.op for condition in result.state.conditions], ['bvsge'])
        self.assertEqual(result.state.conditions[0].args[1], bits(0x1100, 64))
        implied = [row for row in result.state.reports if row['kind'] == 'source_implied_ram_guard']
        self.assertEqual([row['endpoint'] for row in implied], ['ram_base', 'ram_end'])
        self.assertTrue(all(row['source_intervals'] == self.rows for row in implied))
        # Without a source interval every guard stays a path condition.
        bare, = evaluate_trace(trace, SymbolicState(registers={'x2': self.pointer}))
        self.assertEqual(len(bare.state.conditions), 3)

    def test_copy_preserves_bounds_without_changing_original(self):
        state = SymbolicState(source_intervals=self.rows)
        copy = state.copy()
        copy.source_intervals.clear()
        self.assertEqual(len(state.source_intervals), 1)


class JoinGuardTests(unittest.TestCase):
    def setUp(self):
        self.pointer = input_expr('pointer', 64)
        self.intervals = [{'expression': self.pointer.to_dict(), 'minimum': 4096, 'maximum': 8192,
                           'origin': {'source': 'fixture'}}]
        self.returned = input_expr('return_address', 64)
        self.alignments = [{'expression': self.returned.to_dict(), 'modulus': 4, 'residue': 0,
                            'origin': {'source': 'fixture'}}]

    def test_source_interval_excludes_an_unrelated_mmio_equality(self):
        state = SymbolicState(registers={'x2': self.pointer}, source_intervals=self.intervals)
        source = '''(trace (declare-const p (_ BitVec 64)) (read-reg |x2| nil p)
          (assert (= ((_ zero_extend 64) p) #x00000000000000000000000000000008)))'''
        result, = evaluate_trace(source, state)
        self.assertEqual(result.status, 'infeasible')
        self.assertEqual(result.state.reports[-1]['proof_premises_added'], [])
        self.assertTrue(result.state.reports[-1]['required_rocq_guard_projection'])

    def test_existing_alignment_excludes_the_ret_fault_guard(self):
        state = SymbolicState(registers={'x1': self.returned}, source_alignments=self.alignments)
        source = '''(trace (declare-const ret (_ BitVec 64)) (read-reg |x1| nil ret)
          (define-const target (bvand ret #xfffffffffffffffe))
          (assert (= ((_ extract 0 0) (bvlshr target #x0000000000000001)) #b1)))'''
        result, = evaluate_trace(source, state)
        self.assertEqual(result.status, 'infeasible')

    def test_aligned_return_mask_reduces_with_its_source_obligation(self):
        state = SymbolicState(registers={'x1': self.returned}, source_alignments=self.alignments)
        source = '''(trace (declare-const ret (_ BitVec 64)) (read-reg |x1| nil ret)
          (write-reg |PC| nil (bvand ret #xfffffffffffffffe)))'''
        result, = evaluate_trace(source, state)
        self.assertEqual(result.state.registers['PC'], self.returned)
        self.assertEqual(result.state.reports[-1]['proof_status'], 'open')
        self.assertEqual(result.state.reports[-1]['proof_premises_added'], [])

    def test_no_alignment_fact_keeps_the_mask_and_fault_path(self):
        state = SymbolicState(registers={'x1': self.returned})
        source = '''(trace (declare-const ret (_ BitVec 64)) (read-reg |x1| nil ret)
          (write-reg |PC| nil (bvand ret #xfffffffffffffffe)))'''
        result, = evaluate_trace(source, state)
        self.assertEqual(result.state.registers['PC'].op, 'bvand')
        self.assertEqual(result.state.reports, [])

    def test_invalid_or_ambiguous_alignment_cannot_remove_the_mask(self):
        source = '''(trace (declare-const ret (_ BitVec 64)) (read-reg |x1| nil ret)
          (write-reg |PC| nil (bvand ret #xfffffffffffffffe)))'''
        cases = [{'modulus': 3}, {'modulus': 0}, {'modulus': True}, {'residue': 1}, {'residue': 4},
                 {'origin': {}}, {'expression': input_expr('other').to_dict()}]
        for changes in cases:
            with self.subTest(changes=changes):
                rows = [{**self.alignments[0], **changes}]
                state = SymbolicState(registers={'x1': self.returned}, source_alignments=rows)
                result, = evaluate_trace(source, state)
                self.assertEqual(result.state.registers['PC'].op, 'bvand')
        state = SymbolicState(registers={'x1': self.returned}, source_alignments=self.alignments * 2)
        result, = evaluate_trace(source, state)
        self.assertEqual(result.state.registers['PC'].op, 'bvand')

    def test_mask_cannot_remove_an_unknown_bit(self):
        state = SymbolicState(registers={'x1': self.returned}, source_alignments=self.alignments)
        source = '''(trace (declare-const ret (_ BitVec 64)) (read-reg |x1| nil ret)
          (write-reg |PC| nil (bvand ret #xfffffffffffffffb)))'''
        result, = evaluate_trace(source, state)
        self.assertEqual(result.state.registers['PC'].op, 'bvand')

    def test_overlapping_intervals_cannot_exclude_equality(self):
        state = SymbolicState(registers={'x2': self.pointer}, source_intervals=self.intervals)
        source = '''(trace (declare-const p (_ BitVec 64)) (read-reg |x2| nil p)
          (assert (= p #x0000000000001000)))'''
        result, = evaluate_trace(source, state)
        self.assertEqual(result.status, 'complete')

    def test_missing_interval_origin_cannot_exclude_equality(self):
        state = SymbolicState(registers={'x2': self.pointer},
                              source_intervals=[{**self.intervals[0], 'origin': {}}])
        source = '''(trace (declare-const p (_ BitVec 64)) (read-reg |x2| nil p)
          (assert (= p #x0000000000000008)))'''
        result, = evaluate_trace(source, state)
        self.assertEqual(result.status, 'complete')

    def test_copy_and_serialization_keep_alignment_provenance(self):
        state = SymbolicState(source_alignments=self.alignments)
        cloned = state.copy()
        self.assertEqual(cloned.to_dict()['source_alignments'], self.alignments)
        cloned.source_alignments.clear()
        self.assertEqual(state.source_alignments, self.alignments)

    def test_unsigned_and_signed_endpoint_checks_keep_their_meaning(self):
        word = input_expr('narrow', 8)
        rows = [{'expression': word.to_dict(), 'minimum': 240, 'maximum': 250,
                 'origin': {'source': 'fixture'}}]
        signed = operation('bvsgt', word, bits(0, 8))
        unsigned = operation('bvugt', word, bits(0, 8))
        result = _source_comparison_refutation(signed, rows)
        self.assertEqual(result['interval'], [-16, -6])
        self.assertTrue(result['signed'])
        self.assertIsNone(_source_comparison_refutation(unsigned, rows))

    def test_signed_interval_crossing_the_sign_bit_refuses(self):
        word = input_expr('narrow', 8)
        rows = [{'expression': word.to_dict(), 'minimum': 120, 'maximum': 140,
                 'origin': {'source': 'fixture'}}]
        self.assertIsNone(_source_comparison_refutation(operation('bvsgt', word, bits(0, 8)), rows))

    def test_symbolic_endpoint_refuses(self):
        guard = operation('bvult', self.pointer, input_expr('endpoint'))
        self.assertIsNone(_source_comparison_refutation(guard, self.intervals))

    def test_reversed_constant_endpoint_uses_the_same_source_interval(self):
        guard = operation('bvugt', bits(8, 64), self.pointer)
        result = _source_comparison_refutation(guard, self.intervals)
        self.assertEqual(result['comparison'], 'bvult')
        self.assertFalse(result['signed'])

    def test_modular_wrap_ambiguity_cannot_prune_a_comparison(self):
        word = input_expr('narrow', 8)
        rows = [{'expression': word.to_dict(), 'minimum': 250, 'maximum': 255,
                 'origin': {'source': 'fixture'}}]
        wrapped = operation('bvadd', word, bits(2, 8))
        self.assertIsNone(_source_comparison_refutation(operation('bvule', wrapped, bits(1, 8)), rows))


if __name__ == '__main__':
    unittest.main()
