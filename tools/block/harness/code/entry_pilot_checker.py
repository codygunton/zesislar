"""Source controls for inline entry attempts. This module launches no proof."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re

from complete_goals_mcp import check_kernel_groups


INLINE_FIELDS = {"at", "components", "lets", "existentials", "loop", "continuation",
                 "introduction", "annotations", "additional_definitions"}


def validate_auxiliaries(body):
    """Accept only the constructor's structured auxiliary declarations."""
    helpers = body.get("additional_definitions", [])
    if not isinstance(helpers, list):
        raise ValueError("The inline helpers need an ordered list.")
    roles = set()
    for helper in helpers:
        if not isinstance(helper, dict) or set(helper) != {
                "position", "role", "suffix", "handwritten_owner", "body"}:
            raise ValueError("An inline helper has unsupported fields.")
        if helper["position"] not in {"before", "after"} or helper["role"] not in {"entry_variant", "body"}:
            raise ValueError("An inline helper has an unsupported role or position.")
        suffix = helper["suffix"]
        if not isinstance(suffix, str) or (suffix and not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", suffix)):
            raise ValueError("An inline helper has an invalid suffix.")
        if (helper["role"] == "body" and suffix) or (helper["role"] == "entry_variant" and not suffix):
            raise ValueError("An inline helper suffix conflicts with its role.")
        key = (helper["role"], suffix)
        if key in roles:
            raise ValueError("The inline helpers repeat a declaration role.")
        roles.add(key)
        owner = helper["handwritten_owner"]
        if not isinstance(owner, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", owner):
            raise ValueError("An inline helper has an invalid owner.")
        nested = helper["body"]
        if not isinstance(nested, dict) or "components" not in nested or set(nested) - {
                "components", "source_policy", "lets", "existentials", "loop", "continuation", "parameter_order"}:
            raise ValueError("An inline helper needs a structured body without nested declarations.")
        if "source_policy" in nested and not isinstance(nested["source_policy"], str):
            raise ValueError("An inline helper source policy must be a name.")
        if "parameter_order" in nested and nested["parameter_order"] != "free_source_order":
            raise ValueError("An inline helper has an unsupported parameter order.")
        validate_inline_shape(nested)


def validate_inline_shape(body):
    """Check container types before the constructor validates expressions."""
    if not isinstance(body["components"], list) or not all(isinstance(v, dict) for v in body["components"]):
        raise ValueError("The inline body needs an ordered component list.")
    for field in ("lets", "existentials"):
        if field in body and not isinstance(body[field], list):
            raise ValueError("The inline body needs an ordered binder list.")
    for field in ("continuation", "introduction", "annotations"):
        if field in body and not isinstance(body[field], dict):
            raise ValueError("The inline body needs an object field.")
    if "loop" in body and body["loop"] is not None and not isinstance(body["loop"], dict):
        raise ValueError("The inline loop field needs an object or null.")


def strict_loads(text):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("The JSON input repeats a key.")
            result[key] = value
        return result
    def nonfinite(_):
        raise ValueError("The JSON input contains a nonfinite value.")
    return json.loads(text, object_pairs_hook=unique, parse_constant=nonfinite)


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def bound_json(path, expected):
    path = Path(path)
    payload = path.read_bytes()
    if hashlib.sha256(payload).hexdigest() != expected:
        raise ValueError("A bound private input changed.")
    return strict_loads(payload)


def validate_inline(response, case):
    if not isinstance(response, dict) or set(response) != {"schema", "case_id", "body"}:
        raise ValueError("The inline response has unsupported fields.")
    if response["schema"] != "entry-pilot.inline-body.v1" or response["case_id"] != case["case_id"]:
        raise ValueError("The inline response names a different case.")
    body = response["body"]
    if not isinstance(body, dict) or not {"at", "components"}.issubset(body) or set(body) - INLINE_FIELDS:
        raise ValueError("The inline body has unsupported fields.")
    if body["at"] != case["target_pc"]:
        raise ValueError("The inline body changes the target PC.")
    validate_inline_shape(body)
    validate_auxiliaries(body)
    return deepcopy(body)


def install_inline(author, case, response):
    """Replace one primary body. Preserve only source_policy bookkeeping."""
    if case.get("eligible") is not True or any(case["natural_cut_flags"].values()):
        raise ValueError("The case is outside the primary test set.")
    body = validate_inline(response, case)
    output = deepcopy(author)
    positions = [index for index, row in enumerate(output["bodies"]) if row["at"] == case["target_pc"]]
    if len(positions) != 1:
        raise ValueError("The author input needs one matching primary body.")
    index = positions[0]
    original = output["bodies"][index]
    if original.get("additional_definitions"):
        raise ValueError("The primary body contains an excluded auxiliary declaration.")
    if "source_policy" in original:
        body["source_policy"] = deepcopy(original["source_policy"])
    for helper in body.get("additional_definitions", []):
        policy = original.get("source_policy")
        if not isinstance(policy, str) or not policy:
            raise ValueError("Inline helpers require the primary source policy.")
        nested = helper["body"]
        if nested.get("source_policy", policy) != policy:
            raise ValueError("An inline helper changes the primary source policy.")
        nested["source_policy"] = policy
    if "introduction" in original and "introduction" not in body:
        order = output.get("shared", {}).get("selection_order", {}).get("introductions")
        if order is not None:
            if not isinstance(order, list):
                raise ValueError("The introduction selection needs an ordered list.")
            output["shared"]["selection_order"]["introductions"] = [
                pc for pc in order if pc != case["target_pc"]]
    output["bodies"][index] = body
    return output


def source_scores(truth, response, scorer):
    """Keep private expected values inside the private score record."""
    candidate = deepcopy(response["body"])
    expected_raw = deepcopy(truth["raw_author_body"])
    raw_input_units = scorer(expected_raw, expected_raw)["expected_units"]
    if raw_input_units != truth["raw_body_units"]:
        raise ValueError("The gross raw units differ from the bound truth.")
    bookkeeping_units = int("source_policy" in expected_raw)
    expected_raw.pop("source_policy", None)
    expected_inline = deepcopy(truth["inline_expected_body"])
    expected_inline.pop("source_policy", None)
    raw = scorer(expected_raw, candidate)
    inline = scorer(expected_inline, candidate)
    if raw["expected_units"] + bookkeeping_units != truth["raw_body_units"]:
        raise ValueError("The raw scoring units differ from the bound truth.")
    if inline["expected_units"] != truth["inline_expected_units"]:
        raise ValueError("The inline scoring units differ from the bound truth.")
    return {"visibility": "PRIVATE_CHECKER_ONLY", "gross_raw_units": raw_input_units,
            "excluded_source_policy_units": bookkeeping_units, "raw_representation": raw,
            "inline_representation": inline, "primary_success": None,
            "qualification": "Source scores do not establish logical equivalence."}


def complete_groups(export):
    value = bound_json(export["path"], export["sha256"])
    if export.get("success") is not True or "kernel_groups" not in value:
        raise ValueError("The complete export lacks kernel groups.")
    check_kernel_groups(value, value["kernel_groups"])
    if value["local_definition_export"]["original_state_preserved"] is not True:
        raise ValueError("The export changed the source state.")
    return value["kernel_groups"]


class SelectionStop:
    """Retain both exports around one native selection. Never resume it."""

    def __init__(self):
        self.stopped = False

    async def select(self, *, state, export, bind_before, native_selection, freeze, classify_after):
        if self.stopped:
            raise ValueError("The selection controller already stopped.")
        # Stop the whole controller before any callback can fail.
        self.stopped = True
        before = await export(state)
        before_groups = complete_groups(before)
        binding = bind_before(deepcopy(before_groups))
        required = {"successor_pc", "instr_pre_later_flag", "exact_P", "selecting_fact",
                    "branch_path_condition", "selection_identity"}
        if not isinstance(binding, dict) or set(binding) != required:
            raise ValueError("The selection lacks exact runtime bindings.")
        await freeze({"phase": "before-selection", "export": before, "binding": binding})
        after_state = await native_selection(state, "1: liFindInContext.")
        after = await export(after_state)
        after_groups = complete_groups(after)
        # Preserve unexpected shapes before checking the selected obligation.
        await freeze({"phase": "after-selection", "export": after, "binding": binding})
        verdict = classify_after(deepcopy(after_groups), deepcopy(binding))
        if verdict not in ("exact-P-retained", "P-unfolded", "P-closed", "P-differs"):
            raise ValueError("The selection classifier returned an unsupported result.")
        return {"before": before, "after": after, "binding": binding, "verdict": verdict,
                "requires_review": verdict != "exact-P-retained", "stopped": True}


def native_result(receipts, expected_statements):
    """Require both exact native block results. Ignore text agreement."""
    if set(receipts) != {"predecessor", "successor"}:
        return False
    for side in ("predecessor", "successor"):
        row = receipts[side]
        if (row.get("statement_sha256") != expected_statements[side]
                or row.get("native_tactic") != "zesu_block"
                or row.get("compile_file_success") is not True
                or row.get("verification_method") != "module_m"
                or row.get("assumptions") != []):
            return False
        groups = complete_groups(row["final_export"])
        if any(groups[key] for key in ("goals", "stack", "shelf", "given_up")):
            return False
    return True


class TruthGate:
    """Release model attempts only after every bound truth control passes."""

    def __init__(self, case_ids):
        self.required = set(case_ids)
        if len(self.required) != 19:
            raise ValueError("The pilot needs exactly 19 primary cases.")
        self.passed = set()

    def record(self, case_id, *, both_native_proofs_pass):
        if case_id not in self.required or type(both_native_proofs_pass) is not bool:
            raise ValueError("The truth result names an unsupported case.")
        if both_native_proofs_pass:
            self.passed.add(case_id)
        else:
            self.passed.discard(case_id)

    def require_ready(self):
        if self.passed != self.required:
            raise ValueError("The complete truth gate did not pass.")
