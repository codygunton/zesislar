"""Check entry-only admission without starting Rocq or a machine proof."""
import asyncio
from contextlib import asynccontextmanager
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace
from itertools import count
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / "block"))
import launch_entries


MODULES = ("ZesuSsz.Automation.All", "ZesuSsz.Automation.Approved", "ZesuSsz.Compliance.TestHints")


class EntryTests(unittest.IsolatedAsyncioTestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "ZesuSsz/Evidence").mkdir(parents=True)
        (self.root / "ZesuSsz/Compliance").mkdir()
        (self.root / "ZesuSsz/Compliance/TestHints.v").write_text("(* exact umbrella *)\n")
        (self.root / "ZesuSsz/Evidence/test_function_text.json").write_text(json.dumps({
            "function": "test.function", "registrations": ["ZesuSsz/Compliance/TestHints.v"]}))
        self.artifacts = {}
        for module in MODULES:
            path = self.root / (module + ".vo")
            path.write_bytes(module.encode())
            self.artifacts[module] = launch_entries.file_reference(path)
        self.source = self.root / "Source.v"
        self.source.write_text("".join("Require Import " + module + ".\n" for module in MODULES) +
                               "Lemma entry : True.\nProof.\n  try zesu_block.\nQed.\n")
        self.entry = {"id": "block_1", "source": launch_entries.file_reference(self.source),
                      "theorem": "entry", "artifacts": self.artifacts}
        self.calls = []
        self.opened = []
        self.behavior = {}
        self.active = False

    def identity(self, pid):
        if not self.active:
            raise FileNotFoundError("The fake Pet closed.")
        return {"pid": pid, "start_ticks": 100, "state": "S"}

    @asynccontextmanager
    async def factory(self, directory):
        self.opened.append(directory)
        self.active = True
        owner = self
        class Session:
            async def initialize(self):
                owner.calls.append(("initialize", {}))
                if owner.behavior.get("initialize_failure"):
                    raise ConnectionError("exact initialization failure")
                return {"structuredContent": {"initialized": True}}
            async def call_tool(self, tool, arguments):
                owner.calls.append((tool, arguments))
                if tool == "rocq_health":
                    value = {"success": True, "ok": True}
                elif tool == "rocq_start":
                    text = Path(arguments["file"]).read_text()
                    if "try zesu_block." in text or not text.endswith("Proof.\nAbort.\n"):
                        raise AssertionError("The entry view contains a primary body.")
                    value = {"success": True, "state_id": 1}
                    if owner.behavior.get("refuse_start") or owner.behavior.get("refuse_id") == directory.name:
                        value = {"success": False, "error": "exact refused entry"}
                elif tool == "rocq_diag":
                    value = {"success": True, "pet": {"pid": 44}}
                elif tool == "rocq_query":
                    module = arguments["command"].removeprefix("Locate Library ").removesuffix(".")
                    path = owner.artifacts[module]["path"]
                    if owner.behavior.get("wrong_object"):
                        path += ".different"
                    value = {"success": True, "from_state_id": 1,
                             "output": module + " has been loaded from file " + path}
                    if owner.behavior.get("wrapped_location"):
                        value["output"] = value["output"].replace("from file ", "from file\n", 1)
                    if owner.behavior.get("extra_location_output"):
                        value["output"] += "\nextra output"
                    if owner.behavior.get("boolean_state"):
                        value["from_state_id"] = True
                    if owner.behavior.get("mutate_object"):
                        Path(path).write_bytes(b"changed object")
                    if owner.behavior.get("mutate_source"):
                        owner.source.write_text("changed source")
                elif tool == "rocq_complete_goals":
                    goal = {"info": {"evar": 1}, "hyps": [], "ty": "True"}
                    groups = {"goals": [goal], "stack": [], "shelf": [], "given_up": []}
                    exported = {**groups, "kernel_groups": deepcopy(groups),
                                "local_definition_export": {"original_state_preserved": True}}
                    if owner.behavior.get("missing_kernel"):
                        exported.pop("kernel_groups")
                    path = directory / "complete/state_1.json"
                    path.parent.mkdir(exist_ok=True)
                    path.write_text(json.dumps(exported))
                    value = {"success": True, "state_id": 1, **launch_entries.file_reference(path)}
                    if owner.behavior.get("wrong_export_hash"):
                        value["sha256"] = "0" * 64
                    if owner.behavior.get("outside_export"):
                        outside = owner.root.parent / (owner.root.name + ".outside.json")
                        outside.write_bytes(path.read_bytes())
                        owner.addCleanup(outside.unlink)
                        value.update(launch_entries.file_reference(outside))
                else:
                    raise AssertionError("The preflight requested a forbidden tool: " + tool)
                return {"structuredContent": value, "content": [{"type": "text", "text": "exact raw text"}]}
        try:
            yield Session()
        finally:
            self.active = False
            if self.behavior.get("mutate_at_closure"):
                self.source.write_text("changed during closure")

    async def run_preflight(self, entries=None):
        with patch.object(launch_entries, "process_identity", side_effect=self.identity):
            return await launch_entries.check_entries([self.entry] if entries is None else entries,
                self.root, "test.function", self.root / "output", self.factory)

    async def test_owned_factory_sets_the_goal_exporter_and_python(self):
        captured = {}
        class Parameters:
            def __init__(self, **kwargs):
                captured.update(kwargs)
        class Session:
            async def __aenter__(self): return self
            async def __aexit__(self, *args): return False
        @asynccontextmanager
        async def stdio(parameters, **kwargs):
            yield (None, None)
        modules = {
            'mcp': SimpleNamespace(ClientSession=lambda *args: Session(), StdioServerParameters=Parameters),
            'mcp.client': SimpleNamespace(),
            'mcp.client.stdio': SimpleNamespace(stdio_client=stdio),
        }
        directory = self.root / 'factory'
        directory.mkdir()
        with patch.dict(sys.modules, modules):
            async with launch_entries.owned_sessions('exact-guarded-launcher', self.root)(directory):
                pass
        environment = captured['env']
        self.assertEqual(environment['ZESU_MCP_PYTHON'], sys.executable)
        self.assertEqual(environment['ZESU_ROCQ_MCP_BINARY'],
                         str(Path(launch_entries.__file__).with_name('complete_goals_mcp.sh').resolve()))
        self.assertEqual(environment['ZESU_COMPLETE_GOAL_DIR'], str(directory / 'complete'))
        self.assertEqual(captured['command'], 'exact-guarded-launcher')

    async def test_all_selected_entries_pass_before_release(self):
        second = {**self.entry, "id": "block_2"}
        original = self.source.read_bytes()
        result = await self.run_preflight([self.entry, second])
        self.assertTrue(result["passed"])
        self.assertEqual(result["checked_entries"], 2)
        self.assertEqual(self.source.read_bytes(), original)
        self.assertEqual([tool for tool, _ in self.calls].count("rocq_start"), 2)
        self.assertFalse({"rocq_check", "rocq_compile_file", "rocq_verify"} & {tool for tool, _ in self.calls})
        for row in result["entries"]:
            self.assertTrue(row["normal_context_closure"])
            self.assertTrue(row["owned_pet_exited"])

    async def test_later_refusal_keeps_the_all_entry_barrier_closed(self):
        self.behavior["refuse_id"] = "block_2"
        result = await self.run_preflight([self.entry, {**self.entry, "id": "block_2"}])
        self.assertFalse(result["passed"])
        self.assertEqual(result["checked_entries"], 2)
        self.assertTrue(result["entries"][0]["passed"])
        self.assertFalse(result["entries"][1]["passed"])

    async def test_initialization_exception_remains_retained(self):
        self.behavior["initialize_failure"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])
        path = self.root / "output/block_1/calls/0001-initialize-exception.json"
        self.assertEqual(json.loads(path.read_bytes())["error"], "exact initialization failure")
        self.assertFalse({"rocq_check", "rocq_compile_file", "rocq_verify"} & {tool for tool, _ in self.calls})

    async def test_mutation_during_closure_prevents_release(self):
        self.behavior["mutate_at_closure"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])
        self.assertIsNotNone(result["input_error"])

    async def test_remaining_owned_pet_prevents_release(self):
        clock = count(0, 11)
        with patch.object(launch_entries, "matching_live", return_value=True), \
                patch.object(launch_entries, "time", SimpleNamespace(monotonic=lambda: next(clock))):
            result = await self.run_preflight()
        self.assertFalse(result["passed"])
        self.assertFalse(result["entries"][0]["owned_pet_exited"])

    async def test_refused_entry_retains_raw_and_stops_the_batch(self):
        self.behavior["refuse_start"] = True
        result = await self.run_preflight([self.entry, {**self.entry, "id": "block_2"}])
        self.assertFalse(result["passed"])
        self.assertEqual(len(self.opened), 1)
        files = list((self.root / "output/block_1/calls").glob("*-rocq_start-raw.json"))
        self.assertEqual(json.loads(files[0].read_bytes())["structuredContent"]["error"], "exact refused entry")
        self.assertTrue(result["entries"][0]["normal_context_closure"])
        self.assertTrue(result["entries"][0]["owned_pet_exited"])

    async def test_invalid_later_source_starts_no_session(self):
        bad = deepcopy(self.entry)
        bad["id"] = "block_2"
        bad["source"]["sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            await self.run_preflight([self.entry, bad])
        self.assertEqual(self.opened, [])

    async def test_source_outside_workspace_rejects(self):
        with tempfile.NamedTemporaryFile(suffix=".v") as outside:
            self.entry["source"] = launch_entries.file_reference(outside.name)
            with self.assertRaisesRegex(ValueError, "leaves its workspace"):
                await self.run_preflight()
        self.assertEqual(self.opened, [])

    async def test_missing_hint_import_rejects_before_mcp(self):
        self.source.write_text(self.source.read_text().replace("Require Import ZesuSsz.Compliance.TestHints.\n", ""))
        self.entry["source"] = launch_entries.file_reference(self.source)
        with self.assertRaisesRegex(ValueError, "omits required imports"):
            await self.run_preflight()
        self.assertEqual(self.opened, [])

    async def test_missing_approved_import_rejects_before_mcp(self):
        self.source.write_text(self.source.read_text().replace("Require Import ZesuSsz.Automation.Approved.\n", ""))
        self.entry["source"] = launch_entries.file_reference(self.source)
        with self.assertRaisesRegex(ValueError, "omits required imports"):
            await self.run_preflight()
        self.assertEqual(self.opened, [])

    async def test_incomplete_artifact_map_rejects_before_mcp(self):
        self.entry["artifacts"] = {MODULES[0]: self.artifacts[MODULES[0]]}
        with self.assertRaisesRegex(ValueError, "Every direct Require"):
            await self.run_preflight()
        self.assertEqual(self.opened, [])

    async def test_wrapped_loaded_object_path_is_exact(self):
        self.behavior["wrapped_location"] = True
        result = await self.run_preflight()
        self.assertTrue(result["passed"])

    async def test_extra_loaded_object_output_rejects(self):
        self.behavior["extra_location_output"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])
        self.assertIn("loaded module differs", result["entries"][0]["error"]["message"])

    async def test_wrong_loaded_object_rejects(self):
        self.behavior["wrong_object"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])
        self.assertIn("loaded module differs", result["entries"][0]["error"]["message"])

    async def test_mutated_object_rejects(self):
        self.behavior["mutate_object"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])
        self.assertIn("differs from its binding", result["entries"][0]["error"]["message"])

    async def test_mutated_source_rejects(self):
        self.behavior["mutate_source"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])
        self.assertIn("differs from its binding", result["entries"][0]["error"]["message"])

    async def test_wrong_export_hash_rejects(self):
        self.behavior["wrong_export_hash"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])

    async def test_export_outside_owned_directory_rejects(self):
        self.behavior["outside_export"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])
        self.assertIn("leaves its workspace", result["entries"][0]["error"]["message"])

    async def test_missing_kernel_terms_rejects(self):
        self.behavior["missing_kernel"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])
        self.assertIn("kernel terms", result["entries"][0]["error"]["message"])

    async def test_boolean_query_state_rejects(self):
        self.behavior["boolean_state"] = True
        result = await self.run_preflight()
        self.assertFalse(result["passed"])

    async def test_existing_output_rejects_before_mcp(self):
        (self.root / "output").mkdir()
        with self.assertRaisesRegex(ValueError, "fresh output"):
            await self.run_preflight()
        self.assertEqual(self.opened, [])

    async def test_non_integer_byte_count_rejects(self):
        self.entry["source"]["bytes"] = True
        with self.assertRaisesRegex(ValueError, "invalid type"):
            await self.run_preflight()
        self.assertEqual(self.opened, [])


if __name__ == "__main__":
    unittest.main()
