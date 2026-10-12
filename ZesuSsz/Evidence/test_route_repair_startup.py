"""Check immutable startup sources with synthetic certificates."""
import json
from pathlib import Path
import re
import tempfile
import subprocess
import sys
import unittest

from check_decode_item_route_repair import acceptance, startup_source
import test_decode_item_array_store as array_tests
from test_route_repair_linked_evidence import SyntheticEvidence


class StartupSourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.fixture = SyntheticEvidence(self.root)
        self.bundle = self.fixture.bundle
        self.case = self.bundle["native_cases"][0]

    def tearDown(self):
        self.temp.cleanup()

    def check(self):
        return acceptance(self.fixture.index, self.bundle, self.root)

    def attach(self, record):
        source = Path(record["proof_source"]["path"]).read_text()
        theorem = "DesignedBoundary_800d" + record["block"] if "block" in record else record["theorem"]
        marker = re.search(r"\bLemma " + re.escape(theorem) + r"\b", source)
        prefix = source[:marker.start()] + source[marker.start():].split("\nProof.", 1)[0]
        startup = self.fixture.write("startup/" + theorem + ".v", prefix + "\nProof.\nAbort.\n")
        record["interactive_source"] = startup
        session = next(row for row in self.bundle["sessions"] if row["id"] == record["proof_trace"]["session_id"])
        position = record["proof_trace"]["start_call"]
        self.fixture.mutate_file(session["raw_calls"], lambda calls: calls[position]["arguments"].update(file=startup["path"]))
        for reference in record["proof_trace"]["export_attributions"]:
            self.fixture.mutate_file(reference, lambda data: data.update(source=startup))
        self.fixture.mutate_file(self.bundle["input_index"], lambda data: data["inputs"].update({startup["path"]: startup["sha256"]}))
        self.fixture.refresh_attributions()
        return startup

    def mutate_startup(self, transform):
        reference = self.case["interactive_source"]
        path = Path(reference["path"])
        reference.update(self.fixture.write(str(path.relative_to(self.root)), transform(path.read_text())))
        self.fixture.mutate_file(self.bundle["input_index"], lambda data: data["inputs"].update({reference["path"]: reference["sha256"]}))
        for ref in self.case["proof_trace"]["export_attributions"]:
            self.fixture.mutate_file(ref, lambda data: data.update(source=reference))
        self.fixture.refresh_attributions()

    def test_separate_startup_and_compilation_sources(self):
        for row in self.bundle["native_cases"] + self.bundle["rejections"]:
            self.attach(row)
        self.assertEqual(len(self.check()), 9)

    def command(self, array_store=False):
        index = self.root / "index.json"
        index.write_text(json.dumps(self.fixture.index))
        bundle = self.root / "bundle.json"
        bundle.write_text(json.dumps(self.bundle))
        args = [sys.executable, str(Path(__file__).with_name("check_decode_item_route_repair.py")),
                "--workspace", str(self.root), "--index", str(index), "--results", str(bundle)]
        if array_store:
            args.append("--array-store")
        return subprocess.run(args, capture_output=True, text=True)

    def test_resource_startup_command(self):
        for row in self.bundle["native_cases"] + self.bundle["rejections"]:
            self.attach(row)
        result = self.command()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(json.loads(result.stdout)["native_cases"]), 9)

    def test_array_store_startup_command(self):
        fixture = array_tests.ArrayStoreAcceptanceTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.fixture, self.bundle, self.root = fixture.fixture, fixture.bundle, fixture.root
        for row in self.bundle["native_cases"] + self.bundle["rejections"]:
            self.attach(row)
        result = self.command(array_store=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(json.loads(result.stdout)["native_cases"]), 6)

    def test_changed_startup_declaration_rejected(self):
        self.attach(self.case)
        self.mutate_startup(lambda text: text.replace(" : True.", " : False."))
        with self.assertRaisesRegex(ValueError, "declarations differ"):
            self.check()

    def test_changed_startup_prefix_rejected(self):
        self.attach(self.case)
        self.mutate_startup(lambda text: "Set Printing All.\n" + text)
        with self.assertRaisesRegex(ValueError, "pre-proof prefixes differ"):
            self.check()

    def test_final_prefix_newlines_are_not_normalized(self):
        self.attach(self.case)
        final = Path(self.case["proof_source"]["path"])
        final.write_bytes(final.read_bytes().replace(b"\n", b"\r\n"))
        with self.assertRaisesRegex(ValueError, "declarations differ|prefixes differ"):
            startup_source(self.case, final, "DesignedBoundary_800d" + self.case["block"], self.root)

    def test_missing_startup_hash_rejected(self):
        self.attach(self.case)
        self.case["interactive_source"].pop("sha256")
        with self.assertRaises(KeyError):
            self.check()

    def test_unsealed_startup_rejected(self):
        reference = self.attach(self.case)
        self.fixture.mutate_file(self.bundle["input_index"], lambda data: data["inputs"].pop(reference["path"]))
        self.fixture.refresh_attributions()
        with self.assertRaisesRegex(ValueError, "absent from the seal"):
            self.check()

    def test_compilation_source_export_rejected(self):
        self.attach(self.case)
        reference = self.case["proof_trace"]["export_attributions"][0]
        self.fixture.mutate_file(reference, lambda data: data.update(source=self.case["proof_source"]))
        with self.assertRaisesRegex(ValueError, "attribution"):
            self.check()

    def test_compilation_source_start_rejected(self):
        self.attach(self.case)
        session = self.bundle["sessions"][0]
        position = self.case["proof_trace"]["start_call"]
        self.fixture.mutate_file(session["raw_calls"], lambda calls: calls[position]["arguments"].update(file=self.case["proof_source"]["path"]))
        with self.assertRaisesRegex(ValueError, "proof started"):
            self.check()

    def test_nonempty_startup_proof_rejected(self):
        self.attach(self.case)
        self.mutate_startup(lambda text: text.replace("Abort.", "exact I. Abort."))
        with self.assertRaisesRegex(ValueError, "empty Proof/Abort"):
            self.check()

    def test_final_compilation_stays_bound(self):
        reference = self.attach(self.case)
        session = self.bundle["sessions"][0]
        position = self.case["compilation"]["call"]
        self.fixture.mutate_file(session["raw_calls"], lambda calls: calls[position]["arguments"].update(file=reference["path"]))
        with self.assertRaisesRegex(ValueError, "compilation has a different source"):
            self.check()


if __name__ == "__main__":
    unittest.main()
