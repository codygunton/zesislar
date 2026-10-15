"""Check retained I75 diagnostics without treating them as native certificates."""
import argparse
import hashlib
import json
import re
from pathlib import Path

from check_decode_item_route_repair import bound_file, declaration, require

ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "ZesuSsz/Evidence/i75/INDEX.json"
FROZEN_ROOT = "e17a8888ac3aed392397113fb97d0a244a2bba6e"
CLEANUP_STATUS = "unavailable since the 2026-10-15 cleanup; hash retained"


def archived(reference, root=ROOT):
    record = dict(reference)
    record["path"] = record.get("archive_path", record["path"])
    try:
        return bound_file(record, root)[1]
    except FileNotFoundError:
        path = Path(record["path"])
        path = (path if path.is_absolute() else root / path).resolve()
        require(".worktrees" in path.parts and record.get("status") == CLEANUP_STATUS
                and isinstance(record.get("sha256"), str)
                and re.fullmatch(r"[0-9a-f]{64}", record["sha256"]) is not None,
                "A missing I75 artifact lacks the exact cleanup status: " + str(path))
        return None


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
    unavailable = []

    def observed(reference):
        data = archived(reference, root)
        if data is None:
            unavailable.append({key: reference[key] for key in ("path", "archive_path", "sha256", "status")
                                if key in reference})
        return data

    main_bytes = observed(index["main_record"])
    correction_bytes = observed(index["context_correction"])
    require(main_bytes is not None and correction_bytes is not None,
            "The retained metadata reports are required for I75 comparisons.")
    main = json.loads(main_bytes)
    correction = json.loads(correction_bytes)
    require(main["root"] == FROZEN_ROOT and correction["root"] == FROZEN_ROOT,
            "A retained report uses another root.")
    require(main["scope"] == index["scope"], "The activation scope differs.")
    archive_bytes = observed(index["archive_index"])
    archive = json.loads(archive_bytes) if archive_bytes is not None else None
    for key in ("S132_inventory", "archive_scan"):
        observed(index[key])
    if archive is not None:
        records = {(row["source_path"], row["sha256"]): row for row in archive["records"]}
        for path, digest in main["references"].items():
            require((path, digest) in records, "A consolidated reference is absent from the archive.")
    checked_sources, checked_exports = 0, 0
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
        source_bytes = observed(case["source"])
        if source_bytes is not None:
            statement = declaration(source_bytes.decode(), "DesignedBoundary_800d" + case["block"])
            require(hashlib.sha256(statement.encode()).hexdigest() == case["statement_sha256"],
                    "The exact frozen declaration differs.")
            checked_sources += 1
        export_bytes = observed(case["final_export"])
        if export_bytes is not None:
            export = json.loads(export_bytes)
            require(groups(export) == case["actual_groups"], "The actual goal groups differ.")
            require(groups(export["kernel_groups"]) == case["actual_groups"],
                    "The kernel group export differs.")
            checked_exports += 1
    observation = correction["observation"]
    require(observation["syntactic_kind"] == "non-evar" and
            "?Goal5" in observation["printed_term"] and
            observation["substitutions_identical"] is True,
            "The correction must retain the unresolved printed root.")
    require(index["repair_ON"] == "pending B's verified repair",
            "This evidence unit cannot release the future native pass.")
    if check_archive and archive is not None:
        seen = set()
        for record in archive["records"]:
            if record["sha256"] not in seen:
                data = archived({"path": record["source_path"], **record}, root)
                require(len(data) == record["bytes"], "An archived object has another size.")
                seen.add(record["sha256"])
        require(len(seen) == archive["unique_objects"], "The archive object count differs.")
    return {"diagnostic_boundaries": len(cases), "native_closure_claim": False,
            "concrete_6960_witness_claim": False, "repair_ON_started": False,
            "retained_metadata_and_groups_verified": True,
            "archive_reference_coverage": "verified" if archive is not None else CLEANUP_STATUS,
            "raw_sources_verified": checked_sources, "raw_exports_verified": checked_exports,
            "archive_objects_verified": len(seen) if check_archive and archive is not None else 0,
            "unavailable_artifacts": unavailable,
            "limits": "Retained reports support metadata comparisons. Missing archive/source/export bytes were not verified."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-archive", action="store_true")
    args = parser.parse_args()
    print(json.dumps(check(json.loads(INDEX.read_text()), check_archive=args.check_archive)))


if __name__ == "__main__":
    main()
