"""Check retained I75 diagnostics without treating them as native certificates."""
import argparse
import hashlib
import json
from pathlib import Path

from check_decode_item_route_repair import bound_file, declaration, require

ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "ZesuSsz/Evidence/i75/INDEX.json"
FROZEN_ROOT = "e17a8888ac3aed392397113fb97d0a244a2bba6e"


def archived(reference, root=ROOT):
    record = dict(reference)
    record["path"] = record.get("archive_path", record["path"])
    return bound_file(record, root)[1]


def groups(export):
    return {"active": len(export["goals"]),
            "stack": sum(len(left) + len(right) for left, right in export["stack"]),
            "shelf": len(export["shelf"]), "given_up": len(export["given_up"])}


def check(index, root=ROOT, check_archive=False):
    require(index["version"] == 1 and index["frozen_root"] == FROZEN_ROOT,
            "The I75 version or frozen root differs.")
    require(index["native_closure_claim"] is False and
            index["first_global_chronology_claim"] is False and
            index["concrete_6960_witness_claim"] is False,
            "The diagnostic cannot establish native closure or a concrete witness.")
    main = json.loads(archived(index["main_record"], root))
    correction = json.loads(archived(index["context_correction"], root))
    require(main["root"] == FROZEN_ROOT and correction["root"] == FROZEN_ROOT,
            "A retained report uses another root.")
    require(main["scope"] == index["scope"], "The activation scope differs.")
    archive = json.loads(archived(index["archive_index"], root))
    records = {(row["source_path"], row["sha256"]): row for row in archive["records"]}
    for path, digest in main["references"].items():
        require((path, digest) in records, "A consolidated reference is absent from the archive.")
    cases = index["diagnostic_cases"]
    require(len(cases) == len(main["native_boundaries"]), "A diagnostic boundary is missing.")
    for case, boundary in zip(cases, main["native_boundaries"]):
        for field in ("attempt", "block", "statement_sha256", "actual_groups", "stopped"):
            require(case[field] == boundary[field], "A retained diagnostic field differs: " + field)
        for field, original in (("source", boundary["source"]),
                                ("final_export", boundary["final_export"])):
            require(case[field]["path"] == original["path"] and
                    case[field]["sha256"] == original["sha256"],
                    "A diagnostic source or export differs from its main record.")
        source = archived(case["source"], root).decode()
        statement = declaration(source, "DesignedBoundary_800d" + case["block"])
        require(hashlib.sha256(statement.encode()).hexdigest() == case["statement_sha256"],
                "The exact frozen declaration differs.")
        export = json.loads(archived(case["final_export"], root))
        require(groups(export) == case["actual_groups"], "The actual goal groups differ.")
        require(groups(export["kernel_groups"]) == case["actual_groups"],
                "The kernel group export differs.")
    observation = correction["observation"]
    require(observation["syntactic_kind"] == "non-evar" and
            "?Goal5" in observation["printed_term"] and
            observation["substitutions_identical"] is True,
            "The correction must retain the unresolved printed root.")
    require(index["repair_ON"] == "pending B's verified repair",
            "This evidence unit cannot release the future native pass.")
    if check_archive:
        seen = set()
        for record in archive["records"]:
            if record["sha256"] not in seen:
                data = archived({"path": record["source_path"], **record}, root)
                require(len(data) == record["bytes"], "An archived object has another size.")
                seen.add(record["sha256"])
        require(len(seen) == archive["unique_objects"], "The archive object count differs.")
    return {"diagnostic_boundaries": len(cases), "native_closure_claim": False,
            "concrete_6960_witness_claim": False, "repair_ON_started": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-archive", action="store_true")
    args = parser.parse_args()
    print(json.dumps(check(json.loads(INDEX.read_text()), check_archive=args.check_archive)))


if __name__ == "__main__":
    main()
