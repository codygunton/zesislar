"""Check ELF extent and permission extraction for the stock map."""
import unittest
from generate import load_sections


class LoadSectionTests(unittest.TestCase):
    def section(self, **changes):
        segment = dict(p_type='PT_LOAD', p_vaddr=0x1000,
                       p_memsz=0x20, p_filesz=0x10, p_flags=5)
        segment.update(changes)
        return dict(elf_layout=dict(segments=[segment]))

    def test_permissions(self):
        for flags in range(8):
            with self.subTest(flags=flags):
                section, = load_sections(self.section(p_flags=flags))
                self.assertEqual(section['sectionReadable'], bool(flags & 4))
                self.assertEqual(section['sectionWritable'], bool(flags & 2))
                self.assertEqual(section['sectionExecutable'], bool(flags & 1))

    def test_memory_and_file_extents(self):
        section, = load_sections(self.section(p_filesz=0))
        self.assertEqual(section['sectionBase'], 0x1000)
        self.assertEqual(section['sectionEnd'], 0x1020)
        self.assertEqual(section['sectionFileEnd'], 0x1000)

    def test_reject_invalid_extent(self):
        for changes in [dict(p_filesz=0x21), dict(p_memsz=-1),
                        dict(p_vaddr=(1 << 64)-1), dict(p_flags=8)]:
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                load_sections(self.section(**changes))

    def test_ignore_nonload_segment(self):
        self.assertEqual(load_sections(self.section(p_type='PT_NOTE')), [])


if __name__ == '__main__':
    unittest.main()
