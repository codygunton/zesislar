import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from generate_islaris_trace_index import generate, lookup_tree


class LookupTreeTest(unittest.TestCase):
    def test_balances_addresses_and_keeps_trace_names(self):
        lines = lookup_tree([
            (0x100, "Trace.a100"),
            (0x104, "Trace.a104"),
            (0x108, "Trace.a108"),
        ])
        source = "\n".join(lines)
        self.assertIn("Z.compare address 0x104", source)
        self.assertIn("Some (Trace.a100)", source)
        self.assertIn("Some (Trace.a108)", source)
        self.assertEqual(source.count("match Z.compare"), 3)

    def test_uses_requested_theory_prefix(self):
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            dump_dir = root / "dumps"
            output_dir = root / "index"
            dump_dir.mkdir()
            (dump_dir / "block_0.dump").write_text(
                "100: 00000013 nop\n"
            )
            generate(dump_dir, output_dir, 0, "example")
            self.assertIn(
                "IslaTraces.example_0.a100.a100",
                (output_dir / "Index.v").read_text(),
            )
            self.assertIn(
                "(name IslaTraces.example_blocks)",
                (output_dir / "dune").read_text(),
            )

if __name__ == "__main__":
    unittest.main()
