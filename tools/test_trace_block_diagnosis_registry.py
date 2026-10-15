"""Check exact observer bindings and truthful diagnosis metadata."""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).parent / "block"))
from trace_block_filtered import typed_guards, bind_descriptors
from trace_block_filtered_points import stable_capture_lazy
from test_trace_block_filtered_points import capture

class RegistryTests(unittest.TestCase):
    def test_memory_guards_have_switch_independent_shapes(self):
        guards = typed_guards()
        for client, head in [("MemoryAccess.Hooks", "envs_entails _ (find_in_context (FindMemMapsTo _) _)"), ("MemoryAccess.FindInContext", "FindInContext (FindMemMapsTo _) _")]:
            with self.subTest(client=client):
                self.assertIn(head, guards[client])
                self.assertIn("ltac1:(idtac)", guards[client])
                self.assertIn("ltac1val:(fun _ =>", guards[client])
                self.assertNotIn("ZesuStep", guards[client])
                bound = bind_descriptors({client: {"rule": "MemoryAccess", "commands": {"whole-rule": "exact I"}, "log_filter": []}})
                self.assertEqual(bound[client]["typed_guard"]["command"], guards[client])
    def test_memory_wrong_rule_rejects(self):
        with self.assertRaisesRegex(ValueError, "different rule"):
            bind_descriptors({"MemoryAccess.Hooks": {"rule": "ReturnRoute"}})
    def test_snapshot_missing_observations_is_explicit(self):
        self.assertEqual(stable_capture_lazy(capture())["completeness"], {"required_fields_complete": True, "missing_observations": []})
