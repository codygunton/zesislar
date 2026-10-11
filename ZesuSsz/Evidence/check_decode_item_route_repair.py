"""Check actual native route-repair certificates against the frozen nine-site set."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "ZesuSsz/Evidence/route_repair/INDEX.json"
SITES = ["6960", "697c", "69e8", "6a08", "6a38", "6aa8", "6ad8", "6a24", "6ac4"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bound_file(reference, root=ROOT):
    path = Path(reference["path"])
    if not path.is_absolute():
        path = root / path
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == reference["sha256"],
            "A bound file changed: " + str(path))
    return path, data


def declaration(source, name):
    match = re.search(r"\bLemma " + re.escape(name) + r"\b", source)
    require(match is not None, "The exact native theorem is missing: " + name)
    return source[match.start():].split("\nProof.", 1)[0].strip()


def response(call):
    raw = call["raw_response"]
    structured = raw.get("structuredContent")
    if structured is not None:
        return structured
    for item in raw.get("content", []):
        if item.get("type") == "text":
            try:
                return json.loads(item["text"])
            except json.JSONDecodeError:
                pass
    raise ValueError("The raw tool response contains no structured result.")


def closed_groups(data):
    require(set(data) == {"goals", "stack", "shelf", "given_up"},
            "The export does not contain all four actual groups.")
    require(not data["goals"] and not data["shelf"] and not data["given_up"] and
            not data["stack"], "An actual native group remains open.")


def inventory(index, root=ROOT):
    require([case["block"] for case in index["cases"]] == SITES,
            "The acceptance inventory must contain the exact nine sites.")
    for case in index["cases"]:
        _, statement = bound_file(case["native_statement"], root)
        _, source = bound_file(case["native_source"], root)
        require(declaration(source.decode(), case["native_theorem"]) ==
                statement.decode().strip(), "The captured native statement changed.")
        bound_file(case["capture"], root)
    bound_file(index["checked_module_source"], root)
    bound_file(index["control_module"], root)
    bound_file(index["reviewed_terminal_package"], root)


def successful(calls, tool):
    return [call for call in calls if call["tool"] == tool and response(call).get("success") is True]


def native_case(case, record, index, root=ROOT):
    source_path, source_bytes = bound_file(record["proof_source"], root)
    source = source_bytes.decode()
    _, expected = bound_file(case["native_statement"], root)
    require(declaration(source, case["native_theorem"]) == expected.decode().strip(),
            "The repair changed the exact native closure statement.")
    _, original_bytes = bound_file(case["native_source"], root)
    original = original_bytes.decode()
    marker = "Lemma " + case["native_theorem"]
    switch_line = "Require Import " + index["repair_identity"]["module"] + "."
    prefix = source.split(marker, 1)[0].replace(switch_line + "\n", "")
    require(prefix == original.split(marker, 1)[0],
            "The repair changed a native entry definition or declaration environment.")
    for module in index["ON_imports"]:
        require(re.search(r"Require (?:Import|Export) " + re.escape(module) + r"\.", source),
                "The proof lacks its required ON import: " + module)
    object_path, _ = bound_file(record["compiled_object"], root)
    require(object_path.suffix == ".vo" and object_path.stem == source_path.stem,
            "The native object does not match the compiled source name.")
    _, raw = bound_file(record["raw_calls"], root)
    calls = json.loads(raw)
    require(successful(calls, "rocq_health"), "The native health check is missing.")
    starts = successful(calls, "rocq_start")
    require(any(call["arguments"].get("theorem") == case["native_theorem"] and
                Path(call["arguments"]["file"]).resolve() == source_path.resolve()
                for call in starts), "The native source did not start in MCP.")
    identity = index["repair_identity"]
    query = "Check (_ : " + identity["class"] + ")."
    require(any(call["arguments"].get("command") == query
                for call in successful(calls, "rocq_query")),
            "The actual ON class did not resolve in the native session.")
    require(any(call["arguments"].get("command") == "Print " + identity["instance"] + "."
                for call in successful(calls, "rocq_query")),
            "The actual repair instance did not resolve in the native session.")
    checks = successful(calls, "rocq_check")
    require(any("zesu_block" in call["arguments"].get("body", "") for call in checks),
            "No successful native block proof request is bound.")
    finals = successful(calls, "rocq_complete_goals")
    final = record["actual_final"]
    require(any(response(call) == final for call in finals),
            "The final export is not an actual MCP response.")
    require(final.get("groups_are_actual") is True and final.get("truncated") is False and
            final.get("source_sha256") == hashlib.sha256(source_bytes).hexdigest() and
            final.get("theorem") == case["native_theorem"],
            "The final native export has a different identity.")
    _, groups_bytes = bound_file({"path": final["path"], "sha256": final["sha256"]}, root)
    closed_groups(json.loads(groups_bytes))
    require(any(call["arguments"].get("body", "").strip() == "Qed." and
                call["arguments"].get("from_state") == final["state_id"] for call in checks),
            "The native proof did not complete Qed from the empty state.")
    require(any(Path(call["arguments"].get("file", "")).resolve() == source_path.resolve()
                for call in successful(calls, "rocq_compile_file")),
            "The exact native source did not compile through MCP.")
    verifies = successful(calls, "rocq_verify")
    require(any(call["arguments"].get("proof") == source and
                case["native_theorem"] in call["arguments"].get("problem_statement", "") and
                declaration(call["arguments"]["problem_statement"], case["native_theorem"]) ==
                expected.decode().strip() and response(call).get("assumptions") == [] and
                response(call).get("verification_method") in ("module_m", "shared_defs")
                for call in verifies), "The exact native statement lacks an empty-assumption certificate.")
    _, closure_bytes = bound_file(record["owned_closures"], root)
    closures = json.loads(closure_bytes)
    require(closures and all(row["transport_closed_normally"] and row["server_exit_verified"] and
            row.get("cleanup_signals_sent", 0) == 0 and
            (row.get("Pet_exit_verified") or row.get("standalone_Pet_absent")) for row in closures),
            "An owned native session lacks normal closure evidence.")
    return {"block": case["block"], "actual_groups": [0, 0, 0, 0],
            "methods": [response(call).get("verification_method") for call in verifies],
            "assumptions": []}


def acceptance(index, bundle, root=ROOT):
    inventory(index, root)
    require(bundle["repair_identity"] == {key: index["repair_identity"][key]
            for key in ("module", "class", "instance")}, "The repair switch identity differs.")
    require([row["block"] for row in bundle.get("native_cases", [])] == SITES,
            "Actual native certificates are required for all nine sites.")
    switch_path, switch_bytes = bound_file(bundle["switch_source"], root)
    require(switch_path.resolve() == (root / (index["repair_identity"]["module"].replace(".", "/") + ".v")).resolve(),
            "The switch source is not the reserved production module.")
    require(index["repair_identity"]["instance"] in switch_bytes.decode() and
            index["repair_identity"]["class"] in switch_bytes.decode(),
            "The implementation lacks the reserved class or instance.")
    _, seal_bytes = bound_file(bundle["input_index"], root)
    seal = json.loads(seal_bytes)
    require(seal["root"] == bundle["verification_root"], "The verification root differs from its input seal.")
    for path, sha in seal["inputs"].items():
        bound_file({"path": path, "sha256": sha}, root)
    require(str(switch_path.resolve()) in seal["inputs"], "The actual switch source is not input-bound.")
    results = [native_case(case, row, index, root)
               for case, row in zip(index["cases"], bundle["native_cases"])]
    _, controls = bound_file(index["control_module"], root)
    require([row["theorem"] for row in bundle["rejections"]] == index["reject_controls"],
            "Both S119 wrong-commitment rejections are required.")
    for row in bundle["rejections"]:
        _, raw = bound_file(row["raw_calls"], root)
        calls = json.loads(raw)
        expected = declaration(controls.decode(), row["theorem"])
        require(any(declaration(call["arguments"].get("problem_statement", ""), row["theorem"]) ==
                    expected and response(call).get("assumptions") == []
                    for call in successful(calls, "rocq_verify")),
                "An exact S119 rejection certificate is missing.")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path,
                        help="The hash-bound actual ON native proof bundle.")
    parser.add_argument("--check-inventory", action="store_true",
                        help="Check capture identities only. This does not accept the repair.")
    args = parser.parse_args()
    index = json.loads(INDEX.read_text())
    if args.check_inventory:
        inventory(index)
        print("Nine capture identities checked. Native acceptance did not run.")
        return 0
    require(args.results is not None, "The actual nine-native proof bundle is required.")
    result = acceptance(index, json.loads(args.results.read_text()))
    print(json.dumps({"accepted": True, "native_cases": result, "S119_rejections": 2}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
