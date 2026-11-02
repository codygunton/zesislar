"""Render only typed, source-scoped byte-window predicates."""
from copy import deepcopy
import json
from pathlib import Path
import unittest

try:
    from .loop_widen import render_byte_window_fold
except ImportError:
    from loop_widen import render_byte_window_fold


class ByteWindowFoldRendererTests(unittest.TestCase):
    def setUp(self):
        self.relation = {'kind': 'byte_window_fold', 'register': 'x7', 'index': 'i',
            'word_width': 64, 'digit_width': 8,
            'window': {'function': 'ByteWindowFold.zesu_byte_window_fold',
                'array': {'op': 'input', 'value': 'sourceBytes'},
                'start': 1, 'count': 'Z.to_nat i'}}
        self.scope = {'machine_x7': 'bv 64', 'i': 'lvar "zesuLoopIndex" Z',
                      'sourceBytes': 'list (bv 8)'}

    def test_exact_term_imports_and_input_preservation(self):
        original, scope = deepcopy(self.relation), deepcopy(self.scope)
        expected = ('bv_unsigned machine_x7 = ByteWindowFold.zesu_byte_window_fold '
                    '(sourceBytes) 1%nat (Z.to_nat i)')
        self.relation['term'] = expected
        rendered = render_byte_window_fold(self.relation, scope=self.scope)
        self.assertEqual(rendered['term'], expected)
        self.assertEqual(rendered['imports'], ['Coq.ZArith.ZArith',
            'stdpp.bitvector.definitions', 'ZesuSsz.Automation.ByteWindowFold'])
        self.assertEqual(self.relation, dict(original, term=expected))
        self.assertEqual(self.scope, scope)

    def test_exact_owned_array_and_offset_expressions(self):
        array = 'List.skipn sourceStart sourceBytes'
        offset = '(windowStart + delta)%nat'
        self.relation['window'].update(array={'op': 'input', 'value': array}, start=offset)
        self.scope[array] = 'list (bv 8%N)'
        self.scope[offset] = 'nat'
        self.scope['machine_x7'] = 'bv 64%N'
        rendered = render_byte_window_fold(self.relation, scope=self.scope)
        self.assertEqual(rendered['term'],
            'bv_unsigned machine_x7 = ByteWindowFold.zesu_byte_window_fold '
            '((List.skipn sourceStart sourceBytes)) ((windowStart + delta)%nat) (Z.to_nat i)')

    def test_shared_index_name_is_preserved(self):
        self.relation['index'] = 'sharedIndex'
        self.relation['window']['count'] = 'Z.to_nat sharedIndex'
        scope = dict(self.scope)
        scope['sharedIndex'] = scope.pop('i')
        rendered = render_byte_window_fold(self.relation, scope=scope)
        self.assertTrue(rendered['term'].endswith('(Z.to_nat sharedIndex)'))
        self.assertNotIn('(Z.to_nat i)', rendered['term'])

    def test_source_loop_array_atoms_match_existing_assertions(self):
        data = json.loads((Path(__file__).parent / 'testdata/loop_widen_owned_reads.json').read_text())
        for row in data:
            relation = deepcopy(self.relation)
            relation['register'] = 'x13'
            relation['window']['array'] = row['array']
            relation['term'] = ('bv_unsigned machine_x13 = ByteWindowFold.zesu_byte_window_fold '
                '((decodeItemInputBytes args)) 1%nat (Z.to_nat i)')
            scope = {'machine_x13': 'bv 64', 'i': 'Z',
                     row['array']['value']: 'list (bv 8)'}
            self.assertEqual(render_byte_window_fold(relation, scope=scope)['term'], relation['term'])

    def test_missing_bindings_refuse(self):
        for name in self.scope:
            scope = {key: value for key, value in self.scope.items() if key != name}
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'unbound'):
                render_byte_window_fold(self.relation, scope=scope)
        self.relation['window']['start'] = 'sourceStart'
        with self.assertRaisesRegex(ValueError, 'unbound'):
            render_byte_window_fold(self.relation, scope=self.scope)

    def test_wrong_source_types_refuse(self):
        for name, value in [('machine_x7', 'bv 32'), ('i', 'nat'),
                            ('i', 'lvar "otherIndex" Z'), ('sourceBytes', 'list (bv 16)')]:
            scope = dict(self.scope, **{name: value})
            with self.subTest(name=name, value=value), self.assertRaisesRegex(ValueError, 'source type'):
                render_byte_window_fold(self.relation, scope=scope)
        self.relation['window']['start'] = 'sourceStart'
        with self.assertRaisesRegex(ValueError, 'source type'):
            render_byte_window_fold(self.relation, scope=dict(self.scope, sourceStart='Z'))

    def test_unsupported_structural_shapes_refuse(self):
        for key, value in [('kind', 'other'), ('register', 'x32'), ('word_width', 32),
                           ('word_width', 64.0), ('digit_width', 16), ('index', '_')]:
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                render_byte_window_fold(dict(self.relation, **{key: value}), scope=self.scope)
        for key, value in [('start', -1), ('start', True), ('start', {}),
                           ('count', 'Z.to_nat (i + 1)'), ('function', 'other.fold'),
                           ('array', {'op': 'unknown_input', 'value': 'sourceBytes'}),
                           ('array', {'op': 'input', 'value': 'sourceBytes', 'width': 8}),
                           ('array', {'op': 'input', 'value': 'sourceBytes', 'args': []})]:
            relation = deepcopy(self.relation)
            relation['window'][key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                render_byte_window_fold(relation, scope=self.scope)
        relation = deepcopy(self.relation)
        relation['window']['extra'] = 'ignored'
        with self.assertRaises(ValueError):
            render_byte_window_fold(relation, scope=self.scope)

    def test_supplied_term_cannot_override_the_array_or_index(self):
        with self.assertRaisesRegex(ValueError, 'differs'):
            render_byte_window_fold(dict(self.relation, term='True'), scope=self.scope)
        relation = deepcopy(self.relation)
        relation['window']['array']['value'] = 'otherBytes'
        with self.assertRaisesRegex(ValueError, 'unbound'):
            render_byte_window_fold(relation, scope=self.scope)

    def test_commands_refuse_even_inside_an_explicit_scope_atom(self):
        relation = deepcopy(self.relation)
        term = 'sourceBytes. Axiom injected : False.'
        relation['window']['array']['value'] = term
        with self.assertRaisesRegex(ValueError, 'command or tactic'):
            render_byte_window_fold(relation, scope=dict(self.scope, **{term: 'list (bv 8)'}))


if __name__ == '__main__':
    unittest.main()
