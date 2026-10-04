import hashlib
import json
from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / "build/stock-zisk/inventory.json"
CANDIDATE = ROOT / "ZesuSsz/Contracts/Candidates/ParentHeaderDomain.v"


def inventory_semantic_sha256(inventory):
    semantic = {key: value for key, value in inventory.items()
                if key != "artifact_identity"}
    canonical = json.dumps(semantic, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode()).hexdigest()


class ParentHeaderCandidateMapTest(unittest.TestCase):
    def test_selected_call_map(self):
        source = CANDIDATE.read_text()
        inventory = json.loads(INVENTORY.read_text())
        digest = inventory_semantic_sha256(inventory)
        self.assertIn(f'"{digest}"%string', source)

        schedule = source.split("Definition parentHeaderFieldSchedule", 1)[1]
        schedule = schedule.split("].", 1)[0]
        rows = re.findall(
            r"\(0x([0-9a-f]+), (RequiredSkip|RequiredUint64|OptionalSkip|OptionalUint64)\)",
            schedule,
        )
        self.assertEqual(len(rows), 19)
        sites = [0x800D5CF4] + [int(pc, 16) for pc, _ in rows]

        function = next(row for row in inventory["functions"]
                        if row["name"] == "rlp_decode.decodeParentHeader")
        calls = [row for row in function["calls"] if row["kind"] == "call"]
        self.assertEqual(sites, [row["pc"] for row in calls])

        self.assertEqual([kind for _, kind in rows],
                         ["RequiredSkip"] * 9 + ["RequiredUint64"] * 3 +
                         ["OptionalSkip"] * 3 +
                         ["OptionalUint64", "OptionalSkip", "OptionalUint64",
                          "OptionalUint64"])

        next_uint64 = {0x800D615C, 0x800D621C, 0x800D6250}
        for call in calls:
            target = 0x800D6274 if call["pc"] in next_uint64 else 0x800D6960
            self.assertEqual(call["target"], target)

    def test_identity_rebind_does_not_change_semantic_hash(self):
        inventory = json.loads(INVENTORY.read_text())
        original = inventory_semantic_sha256(inventory)
        inventory["artifact_identity"] = "rebound-identity"
        self.assertEqual(inventory_semantic_sha256(inventory), original)
        inventory["functions"][0]["name"] = "changed-function"
        self.assertNotEqual(inventory_semantic_sha256(inventory), original)


if __name__ == "__main__":
    unittest.main()
