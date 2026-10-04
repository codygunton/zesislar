"""Check that static evidence refuses changed instruction bytes."""
import unittest
from unittest.mock import Mock
import collect


class InstructionTests(unittest.TestCase):
    def elf(self, word):
        section = Mock()
        section.__getitem__ = Mock(side_effect=lambda key: {
            'sh_flags': 4, 'sh_addr': 0x8000, 'sh_size': 4}[key])
        section.data.return_value = word.to_bytes(4, 'little')
        elf = Mock()
        elf.iter_sections.return_value = [section]
        return elf

    def test_changed_word_is_refused(self):
        with self.assertRaisesRegex(ValueError, 'instruction changed'):
            collect.instruction(self.elf(0x00000013), 0x8000, 0x00e68733)

    def test_byte_order_is_explicit(self):
        row = collect.instruction(self.elf(0x00e68733), 0x8000, 0x00e68733)
        self.assertEqual(row['bytes_little_endian'], '3387e600')
        self.assertEqual(row['decoded']['mnemonic'], 'add')


if __name__ == '__main__':
    unittest.main()
