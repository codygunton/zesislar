"""Check generic block selection on a small machine CFG."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from entries import blocks


class BlockEntryTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.cfg = Path(self.directory.name) / 'cfg.json'
        self.cfg.write_text(json.dumps({'functions': [{
            'name': 'decoder', 'rows': [
                {'pc': 4096, 'mnemonic': 'addi', 'kind': 'plain'},
                {'pc': 4100, 'mnemonic': 'jalr', 'kind': 'return'}],
            'blocks': [{'start': 4096, 'end': 4104, 'successors': []}]}]}))

    def test_stock_rows_supply_block_instructions(self):
        result = blocks(self.cfg, {'0x1000': {'module': 'Entry', 'lemma': 'entry'}}, 'decoder')
        self.assertEqual(result[0]['n'], 2)
        self.assertEqual(result[0]['succ'], ['ret'])
        self.assertEqual(result[0]['pick'], ['entry', 'Entry'])

    def test_function_name_is_exact(self):
        with self.assertRaisesRegex(ValueError, 'exactly one function'):
            blocks(self.cfg, {}, 'coder')

    def test_missing_entry_remains_explicit(self):
        self.assertIsNone(blocks(self.cfg, {}, 'decoder')[0]['pick'])


if __name__ == '__main__':
    unittest.main()
