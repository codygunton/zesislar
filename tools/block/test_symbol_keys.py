"""Design tables keyed by function symbol and offset resolve to the address form."""
from pathlib import Path
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from function_profiles import load_profile, resolve_symbol_keys, symbol_table

SYMBOLS = {'mod.function': 0x800d6960, 'mod.callee': 0x800d7000}


class SymbolKeys(unittest.TestCase):
    def table(self, **rows):
        return {'function': 'f', 'symbol': 'mod.function', 'blocks': ['+0x0', '+0x14'], 'loop_heads': ['+0x14'],
                **rows}

    def test_blocks_become_suffixes_under_the_function_prefix(self):
        data = resolve_symbol_keys(self.table(), SYMBOLS)
        self.assertEqual((data['pc_prefix'], data['blocks'], data['loop_heads']), ('0x800d', ['6960', '6974'], ['6974']))
        self.assertEqual(data['symbol'], 'mod.function')

    def test_nested_blocks_keys_and_address_fields(self):
        data = resolve_symbol_keys(self.table(
            loop_designs=[{'head': '+0x14', 'entry_predecessor': '+0x0'}],
            join_designs={'+0x14': ['fact']},
            calls=[{'call_site_pc': '+0x10', 'callee_pc': 'mod.callee+0x0', 'return_site_pc': '+0x14'}]), SYMBOLS)
        self.assertEqual(data['loop_designs'], [{'head': '6974', 'entry_predecessor': '6960'}])
        self.assertEqual(data['join_designs'], {'6974': ['fact']})
        self.assertEqual(data['calls'], [{'call_site_pc': '0x800d6970', 'callee_pc': '0x800d7000',
                                          'return_site_pc': '0x800d6974'}])

    def test_a_relink_changes_only_the_symbol_table(self):
        moved = dict(SYMBOLS, **{'mod.function': 0x800e1230})
        data = resolve_symbol_keys(self.table(), moved)
        self.assertEqual((data['pc_prefix'], data['blocks']), ('0x800e', ['1230', '1244']))

    def test_unknown_symbols_and_bare_addresses_refuse(self):
        with self.assertRaisesRegex(ValueError, 'no symbol'):
            resolve_symbol_keys(self.table(symbol='mod.missing'), SYMBOLS)
        with self.assertRaisesRegex(ValueError, 'hex offset'):
            resolve_symbol_keys(self.table(calls=[{'callee_pc': 'mod.callee'}]), SYMBOLS)
        with self.assertRaisesRegex(ValueError, 'offset from its symbol'):
            resolve_symbol_keys(self.table(blocks=['+0x0', 'mod.callee+0x0']), SYMBOLS)

    def test_a_legacy_table_passes_unchanged(self):
        legacy = {'function': 'f', 'pc_prefix': '0x800d', 'blocks': ['6960']}
        self.assertIs(resolve_symbol_keys(legacy, SYMBOLS), legacy)

    def test_the_committed_symbol_table_names_the_proved_functions(self):
        symbols = symbol_table()
        self.assertEqual(symbols['rlp.decodeItem'], 0x800d6960)
        self.assertEqual(load_profile('decodeItem')['pc_prefix'], '0x800d')
        call, = load_profile('nextUint64')['calls']
        self.assertEqual(call['callee_pc'], hex(symbols['rlp.decodeItem']))


if __name__ == '__main__':
    unittest.main()
