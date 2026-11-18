import sys
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent / "block"))
from return_exit import add_return_precondition, return_blocks, return_package
from render_fp301_statements import render


class ReturnExitTests(unittest.TestCase):
    def inputs(self, root):
        def bound(name, text):
            path = root / name
            path.write_text(text)
            return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}

        source = bound("Return.v", "Definition old `{!islaG Sigma} `{!threadG} "
                       "(args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) "
                       ": iProp Sigma := (owner args ∗ K)%I.\n")
        blocks, callers, cases = [], [], []
        names = [format(0x1000 + n, "x") for n in range(11)]
        for index, name in enumerate(names):
            pc = "0x800d" + name
            row = {"entry_pc": pc, "successor_pcs": ["0x800d2000"]}
            if index == 10:
                row.update(successor_pcs=[], return_clause={"return_instruction_pc": pc})
            blocks.append(row)
            text = ("Lemma DesignedBoundary_800d" + name + " (args : DecodeItemArgs) "
                    "(returnAddress : Z) (K : iProp Sigma) :\n  code -∗ body.\n"
                    "Proof. Abort.\n")
            callers.append({"case": name, "caller": bound(name + ".v", text)})
            cases.append({"pc": pc})
        return {
            "design": bound("design.json", json.dumps({"blocks": blocks})),
            "callers": bound("callers.json", json.dumps({"rows": callers})),
            "declarations": bound("declarations.json", json.dumps({"cases": cases, "sources": []})),
            "return_source": source, "return_symbol": "old", "closed_cases": names[:10],
        }

    def test_complete_render_preserves_closed_statements_and_adds_opacity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inputs = self.inputs(root)
            result = render(inputs, root / "output")
            self.assertEqual(result["changed_blocks"], ["100a"])
            for row in result["statements"][:10]:
                self.assertEqual(row["original_statement_sha256"], row["statement"]["sha256"])
            structural = Path(result["sources"][1]["path"]).read_text()
            self.assertIn("Typeclasses Opaque fp_machineReturn.", structural)

    def test_closed_return_refusal_creates_no_partial_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inputs = self.inputs(root)
            inputs["closed_cases"][-1] = "100a"
            with self.assertRaisesRegex(ValueError, "closed generated statement"):
                render(inputs, root / "refused")
            self.assertFalse((root / "refused").exists())

    def test_exit_kind_comes_from_the_design(self):
        row = {"entry_pc": "0x10", "successor_pcs": [],
               "return_clause": {"return_instruction_pc": "0x14"}}
        self.assertEqual(return_blocks({"blocks": [row]}), {16: row})
        with self.assertRaisesRegex(ValueError, "declared exit kind"):
            return_blocks({"blocks": [{"entry_pc": "0x10", "successor_pcs": []}]})
        row["successor_pcs"] = ["0x20"]
        with self.assertRaisesRegex(ValueError, "inconsistent"):
            return_blocks({"blocks": [row]})

    def test_return_premise_preserves_the_original_statement(self):
        original = "Lemma boundary (args : Args) (K : iProp Sigma) :\n  code -∗ body.\n"
        added = "\n  instr_pre returnAddress (package args K) -∗"
        rendered = add_return_precondition(original, "returnAddress", "package args K")
        self.assertEqual(rendered.replace(added, "", 1), original)
        self.assertIn("(K : iProp Sigma) :" + added, rendered)

    def test_return_body_is_copied_and_used_parameters_cannot_disappear(self):
        source = ("Definition old `{!islaG Sigma} `{!threadG} "
                  "(args : Args) (K : iProp Sigma) (unused : True) : iProp Sigma :=\n"
                  "  ((∃ word : bv 64, owner args word) ∗ K)%I.\n")
        parameters = [{"name": "args", "type": "Args"},
                      {"name": "K", "type": "iProp Sigma"}]
        rendered, record = return_package(source, "old", "generated", parameters)
        self.assertIn(record["body"], rendered)
        self.assertEqual(record["omitted_unused_parameters"],
                         [{"name": "unused", "type": "True"}])
        with self.assertRaisesRegex(ValueError, "occurs"):
            return_package(source.replace("owner args word", "owner args unused word"),
                           "old", "generated", parameters)
        with self.assertRaisesRegex(ValueError, "source types"):
            return_package(source, "old", "generated", [{"name": "args", "type": "Wrong"}])


if __name__ == "__main__":
    unittest.main()
