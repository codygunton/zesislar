#!/usr/bin/env python3
"""Regression checks for the zesu speedscope converter."""

import unittest

from build_zesu_speedscope import (
    COVERED_BY_PROVED_PARENT,
    STATUS_COLUMN,
    convert,
    index_progress,
    resolve_state,
)
from check_zesu_speedscope_payload import check


def core_fixture() -> dict:
    """A three-level tree: a proved parent over an unproved child and a sibling."""
    return {
        "schemaVersion": 3,
        "tree": {
            "uiId": 0,
            "name": "main",
            "self": 1,
            "value": 10,
            "children": [
                {
                    "uiId": 1,
                    "name": "decode",
                    "self": 2,
                    "value": 6,
                    "children": [
                        {"uiId": 2, "name": "inner", "self": 4, "value": 4},
                    ],
                },
                {"uiId": 3, "name": "encode", "self": 3, "value": 3},
            ],
        },
        "meta": [
            {"owner": "fi:0", "qualified": "main", "displayTreeLevel": 0,
             "machineInstructionCount": 1},
            {"owner": "fi:1", "qualified": "decode", "displayTreeLevel": 1,
             "machineInstructionCount": 2},
            {"owner": "fi:2", "qualified": "inner", "displayTreeLevel": 2,
             "machineInstructionCount": 4},
            {"owner": "fi:3", "qualified": "encode", "displayTreeLevel": 1,
             "machineInstructionCount": 3},
        ],
        "total": 10,
        "programTotal": 20,
    }


def progress_fixture() -> dict:
    return {
        "states": [
            {"owner": "fi:0", "qualified": "main", "status": "conditionally_proven"},
            {"owner": "fi:1", "qualified": "decode", "status": "proved",
             "theorem": "decodeInstanceContract"},
            {"owner": "fi:3", "qualified": "encode",
             "status": "contract_specified_assumption"},
        ]
    }


class ConvertTest(unittest.TestCase):
    def setUp(self) -> None:
        self.profile = convert(
            core_fixture(), progress_fixture(), "decode", "flame-details.json"
        )

    def test_totals_match_the_tree(self) -> None:
        profile = self.profile["profiles"][0]
        self.assertEqual(profile["endValue"], 10)
        self.assertEqual(self.profile["zesuProfile"]["total"], 10)
        self.assertEqual(self.profile["zesuProfile"]["programTotal"], 20)
        self.assertEqual(self.profile["zesuProfile"]["scope"], "decode")

    def test_totals_disagreeing_with_the_root_are_rejected(self) -> None:
        core = core_fixture()
        core["tree"]["value"] = 11
        with self.assertRaises(ValueError):
            convert(core, progress_fixture(), "decode", "flame-details.json")

    def test_frame_order_follows_the_generator(self) -> None:
        names = [frame["name"] for frame in self.profile["shared"]["frames"]]
        self.assertEqual(names, ["main", "decode", "inner", "encode"])
        files = [frame["file"] for frame in self.profile["shared"]["frames"]]
        self.assertEqual(files, ["0", "1", "2", "3"])

    def test_call_hierarchy_is_preserved(self) -> None:
        events = self.profile["profiles"][0]["events"]
        self.assertEqual(
            [(event["type"], event["frame"], event["at"]) for event in events],
            [
                ("O", 0, 0),
                ("O", 1, 1),
                ("O", 2, 3),
                ("C", 2, 7),
                ("C", 1, 7),
                ("O", 3, 7),
                ("C", 3, 10),
                ("C", 0, 10),
            ],
        )

    def test_metadata_carries_the_header_fields(self) -> None:
        meta = self.profile["zesuMeta"]
        self.assertEqual(meta[1]["qualified"], "decode")
        self.assertEqual(meta[1]["displayTreeLevel"], 1)
        self.assertEqual(meta[1]["machineInstructionCount"], 2)
        self.assertEqual(meta[1]["theorem"], "decodeInstanceContract")
        self.assertEqual(meta[2]["selfInstructions"], 4)
        self.assertEqual(meta[0]["totalInstructions"], 10)

    def test_full_scope_names_the_full_program(self) -> None:
        full = convert(
            core_fixture(), progress_fixture(), "full", "flame-details-full.json"
        )
        self.assertEqual(full["zesuProfile"]["scope"], "full")
        self.assertEqual(full["zesuProfile"]["detailsUrl"], "flame-details-full.json")
        self.assertIn("full-program", full["profiles"][0]["name"])

    def test_proof_regions_add_a_granular_default_profile(self) -> None:
        progress = progress_fixture() | {
            "regionScope": {
                "label": "sample proof regions",
                "startPc": "0x100",
                "endPc": "0x110",
            },
            "proofRegions": [{
                "label": "proved middle",
                "startPc": "0x104",
                "endPc": "0x10c",
                "status": "unconditionally_proven",
                "theorem": "middle_correct",
            }],
        }
        profile = convert(core_fixture(), progress, "decode", "details.json")

        self.assertEqual(profile["activeProfileIndex"], 1)
        self.assertEqual(profile["profiles"][1]["name"], "writeSuccess proof regions")
        regions = profile["zesuMeta"][-4:]
        self.assertEqual([row["machineInstructionCount"] for row in regions], [4, 1, 2, 1])
        self.assertEqual(regions[2]["theorem"], "middle_correct")


class ProofStateTest(unittest.TestCase):
    def test_every_state_maps_to_a_palette_column(self) -> None:
        self.assertEqual(
            sorted(set(STATUS_COLUMN.values())), [0, 1, 2, 3, 4, 5]
        )

    def test_states_reach_their_own_column(self) -> None:
        for status, column in STATUS_COLUMN.items():
            states = index_progress({"states": [{"owner": "fi:0", "status": status}]})
            resolved = resolve_state({"owner": "fi:0"}, [], states)
            self.assertEqual(STATUS_COLUMN[resolved["status"]], column, status)

    def test_a_proved_parent_covers_an_unproved_child(self) -> None:
        profile = convert(
            core_fixture(), progress_fixture(), "decode", "flame-details.json"
        )
        self.assertEqual(
            profile["shared"]["frames"][2]["col"], COVERED_BY_PROVED_PARENT
        )
        inner = profile["zesuMeta"][2]
        self.assertEqual(inner["status"], "covered_by_proved_parent")
        self.assertEqual(inner["coveringTheorem"], "decodeInstanceContract")

    def test_coverage_does_not_leak_past_an_unproved_parent(self) -> None:
        # `encode` hangs off `main`, which is only conditionally proven, so it
        # keeps its own state rather than inheriting coverage.
        profile = convert(
            core_fixture(), progress_fixture(), "decode", "flame-details.json"
        )
        self.assertEqual(
            profile["zesuMeta"][3]["status"], "contract_specified_assumption"
        )

    def test_a_directly_proved_instance_keeps_its_own_state(self) -> None:
        states = index_progress(progress_fixture())
        resolved = resolve_state(
            {"owner": "fi:1"}, [{"owner": "fi:1"}], states
        )
        self.assertEqual(resolved["status"], "proved")

    def test_the_nearest_proved_ancestor_supplies_the_theorem(self) -> None:
        states = index_progress(
            {
                "states": [
                    {"owner": "a", "status": "proved", "theorem": "outer"},
                    {"owner": "b", "status": "proved", "contract": "inner"},
                ]
            }
        )
        resolved = resolve_state(
            {"owner": "c"}, [{"owner": "a"}, {"owner": "b"}], states
        )
        self.assertEqual(resolved["coveringTheorem"], "inner")

    def test_an_unknown_owner_is_not_started(self) -> None:
        resolved = resolve_state({"owner": "missing"}, [], index_progress({}))
        self.assertEqual(STATUS_COLUMN[resolved["status"]], 0)

    def test_the_machine_owner_resolves_when_the_owner_does_not(self) -> None:
        states = index_progress(
            {"states": [{"owner": "fn:0x10", "status": "proved"}]}
        )
        resolved = resolve_state(
            {"owner": "fi:9", "machineOwner": "fn:0x10"}, [], states
        )
        self.assertEqual(resolved["status"], "proved")


class PayloadCheckTest(unittest.TestCase):
    """The build-time check must reject payloads the viewer would misread.

    Each case damages one claim and expects the check to name it. Without these
    the check could pass by being unable to fail.
    """

    def setUp(self) -> None:
        self.core = core_fixture()
        self.profile = convert(
            core_fixture(), progress_fixture(), "decode", "flame-details.json"
        )

    def test_a_faithful_payload_passes(self) -> None:
        self.assertEqual(check(self.profile, self.core, None, "decode"), [])

    def test_a_repainted_frame_is_rejected(self) -> None:
        self.profile["shared"]["frames"][1]["col"] = 0
        self.assertTrue(check(self.profile, self.core, None, "decode"))

    def test_a_missing_frame_is_rejected(self) -> None:
        self.profile["shared"]["frames"].pop()
        self.assertTrue(check(self.profile, self.core, None, "decode"))

    def test_a_reordered_hierarchy_is_rejected(self) -> None:
        events = self.profile["profiles"][0]["events"]
        # Close `inner` before it opens its parent's sibling, which moves it out
        # of `decode` and up to the root.
        events[2], events[3] = events[3], events[2]
        self.assertTrue(check(self.profile, self.core, None, "decode"))

    def test_coverage_without_a_proved_ancestor_is_rejected(self) -> None:
        # `decode` is the proved parent that covers `inner`. Downgrade it and the
        # coverage `inner` still claims becomes unsupported.
        self.profile["zesuMeta"][1]["status"] = "in_progress"
        self.profile["shared"]["frames"][1]["col"] = STATUS_COLUMN["in_progress"]
        self.assertTrue(check(self.profile, self.core, None, "decode"))

    def test_a_detail_payload_of_the_wrong_length_is_rejected(self) -> None:
        self.assertTrue(check(self.profile, self.core, [{}, {}], "decode"))

    def test_an_unknown_status_is_rejected(self) -> None:
        self.profile["zesuMeta"][0]["status"] = "invented_status"
        self.assertTrue(check(self.profile, self.core, None, "decode"))


if __name__ == "__main__":
    unittest.main()
