import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import gen_block
import regenerate_state_imports


class StateImports(unittest.TestCase):
    def test_generator_uses_reviewed_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / "imports.json"
            manifest.write_text(json.dumps({"states": [{
                "name": "State_test", "imports": ["Contracts.Test"]}]}))
            with patch.object(gen_block, "STATE_IMPORT_MANIFEST", manifest):
                imports = gen_block.state_imports("State_test", ["Legacy.Proof"])
            self.assertIn("Contracts.Test", imports)
            self.assertNotIn("Legacy.Proof", imports)

    def test_sealed_state_preserves_first_definition(self):
        body = ("Definition MemoryRaw : nat := 1.\n"
                "Definition State_test : nat := MemoryRaw.\n")
        source = "Require Import Legacy.Proof.\n\n" + body
        record = {"name": "State_test", "imports": ["Contracts.Test"],
                  "body_sha256": hashlib.sha256(body.encode()).hexdigest()}
        updated = regenerate_state_imports.replace_imports(source, record)
        self.assertTrue(updated.endswith(body))
        with self.assertRaisesRegex(ValueError, "missing definition"):
            regenerate_state_imports.replace_imports(source, dict(record, name="Absent"))

    def test_import_update_preserves_body_and_rejects_changes(self):
        body = "Definition State_test : nat := 1.\nGlobal Opaque State_test.\n"
        source = "(* Generated. *)\nRequire Import Legacy.Proof.\n\n" + body
        record = {"name": "State_test", "imports": ["Contracts.Test"],
                  "body_sha256": hashlib.sha256(body.encode()).hexdigest()}
        updated = regenerate_state_imports.replace_imports(source, record)
        self.assertTrue(updated.endswith(body))
        self.assertNotIn("Legacy.Proof", updated)
        with self.assertRaisesRegex(ValueError, "state body differs"):
            regenerate_state_imports.replace_imports(source.replace(":= 1", ":= 2"), record)


if __name__ == "__main__":
    unittest.main()
