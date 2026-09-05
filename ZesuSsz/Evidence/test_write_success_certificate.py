import copy
import unittest

from check_write_success_certificate import validate
from generate_write_success_certificate import (
    ENTRY_PC,
    EXIT_PC,
    EXPECTED_BACK_EDGES,
    generate,
    render_rocq,
)


def fixture() -> dict:
    # Keep this fixture small.  The source CFG test uses the pinned endpoint
    # CFG, while this graph exercises every certificate rejection path.
    # Each body returns to its loop header, then falls through to the next
    # loop.  This gives DFS the same seven back edges as the pinned CFG.
    loops = sorted(EXPECTED_BACK_EDGES, key=lambda edge: edge[1])
    edges = {ENTRY_PC: [loops[0][1]]}
    for index, (source, target) in enumerate(loops):
        next_header = (loops[index + 1][1]
                       if index + 1 < len(loops) else 0x159D8)
        edges[target] = [source]
        edges[source] = [target, next_header]
    edges[0x159D8] = []
    blocks = []
    for start, successors in edges.items():
        mnemonic = "ret" if start == 0x159D8 else "addi"
        blocks.append({
            "start": start,
            "end": start + 4,
            "successors": [f"0x{target:x}" for target in successors],
            "instructions": [{"pc": start, "mnemonic": mnemonic}],
        })
    return {"artifact": {"identityScope": "ELF PT_LOAD memory image",
                          "sha256": "ab" * 32},
            "functions": [{"name": "ssz_decode_observation.writeSuccess",
                           "blocks": blocks}]}


class WriteSuccessCertificateTests(unittest.TestCase):
    def test_covers_complete_graph_and_seven_back_edges(self):
        certificate = generate(fixture())
        self.assertEqual(certificate["entryPc"], ENTRY_PC)
        self.assertEqual(certificate["exitPcs"], [EXIT_PC])
        self.assertEqual({(row["from"], row["to"])
                          for row in certificate["backEdges"]}, EXPECTED_BACK_EDGES)
        self.assertEqual(certificate["instructionCount"],
                         len(certificate["reachablePcs"]))
        self.assertEqual(certificate["executionInstructionCount"], 950)
        self.assertNotIn("pathBound", certificate)
        self.assertTrue(certificate["exitEdges"])
        phase = {row["pc"]: row["rank"] for row in certificate["phaseRank"]}
        self.assertEqual(set(phase), set(certificate["reachablePcs"]))
        self.assertEqual(certificate["phaseBound"], max(phase.values()) + 1)
        for row in certificate["edges"]:
            if (row["from"], row["to"]) not in EXPECTED_BACK_EDGES:
                self.assertGreater(phase[row["from"]], phase[row["to"]])

    def test_computes_bound_only_with_all_loop_budgets(self):
        cfg = fixture()
        edges = set(EXPECTED_BACK_EDGES)
        certificate = generate(cfg, loop_budgets={edge: 1 for edge in edges})
        self.assertIn("pathBound", certificate)
        self.assertGreater(certificate["pathBound"], 0)
        with self.assertRaisesRegex(ValueError, "missing loop budget"):
            generate(cfg, loop_budgets={next(iter(edges)): 1})

    def test_witness_path_uses_checked_instruction_edges(self):
        certificate = generate(fixture())
        path = certificate["witnessPath"]
        edges = {(row["from"], row["to"])
                 for row in certificate["instructionEdges"]}
        self.assertEqual(path[0], ENTRY_PC)
        self.assertEqual(path[-1], EXIT_PC)
        self.assertTrue(all(edge in edges for edge in zip(path, path[1:])))
        edge_pcs = {pc for edge in edges for pc in edge}
        self.assertLessEqual(set(certificate["reachablePcs"]), edge_pcs)

    def test_renders_rocq_bridge_from_witness(self):
        source = render_rocq(generate(fixture()))
        self.assertIn("Lemma writeSuccessGeneratedTermination", source)
        self.assertIn("Lemma writeSuccessGeneratedBridge", source)
        self.assertNotIn("Admitted.", source)

    def test_rejects_unknown_edge(self):
        cfg = fixture()
        cfg["functions"][0]["blocks"][0]["successors"] = ["0xffff"]
        with self.assertRaisesRegex(ValueError, "unknown CFG edge"):
            generate(cfg)

    def test_rejects_missing_exit(self):
        cfg = fixture()
        cfg["functions"][0]["blocks"][-1]["instructions"][0]["mnemonic"] = "addi"
        with self.assertRaisesRegex(ValueError, "missing return exit"):
            generate(cfg)

    def test_rejects_pc_outside_level1_region(self):
        cfg = fixture()
        cfg["functions"][0]["blocks"][0]["instructions"][0]["pc"] = 0x100
        with self.assertRaisesRegex(ValueError, "outside the Level 1 region"):
            generate(cfg)

    def test_rejects_changed_pinned_identity(self):
        with self.assertRaisesRegex(ValueError, "pinned ELF identities differ"):
            generate(fixture(), expected_sha256="cd" * 32)

    def test_checker_rejects_forged_certificate(self):
        cfg = fixture()
        certificate = generate(cfg, loop_budgets={edge: 1 for edge in EXPECTED_BACK_EDGES})
        forged = copy.deepcopy(certificate)
        forged["pathBound"] += 1
        with self.assertRaisesRegex(ValueError, "does not match"):
            validate(forged, cfg)

    def test_checker_rejects_forged_instruction_edge(self):
        cfg = fixture()
        certificate = generate(cfg)
        forged = copy.deepcopy(certificate)
        forged["instructionEdges"][0]["to"] += 4
        with self.assertRaisesRegex(ValueError, "does not match"):
            validate(forged, cfg)


if __name__ == "__main__":
    unittest.main()
