"""Render declarations only from frozen source-pass alternatives and Level 1 framing."""

from copy import deepcopy
from pathlib import Path
import argparse, hashlib, json, re, sys

parser = argparse.ArgumentParser()
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--input-receipt", type=Path, required=True)
parser.add_argument("--input-receipt-sha256", required=True)
parser.add_argument("--seed-manifest", type=Path, required=True)
parser.add_argument("--seed-manifest-sha256", required=True)
options = parser.parse_args()


def authenticated_json(path, expected):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError("A frozen renderer input changed: " + str(path))
    return json.loads(data)


receipt = authenticated_json(options.input_receipt, options.input_receipt_sha256)
seed_manifest = authenticated_json(options.seed_manifest, options.seed_manifest_sha256)
for binding in [
    receipt[key]
    for key in ["source_pass", "level1_K_source", "vocabulary", "system_shapes"]
] + [seed_manifest[key] for key in ["domain", "seed"]]:
    if (
        hashlib.sha256(Path(binding["path"]).read_bytes()).hexdigest()
        != binding["sha256"]
    ):
        raise ValueError("A frozen renderer source changed: " + binding["path"])
GENERATOR_ROOT = Path(__file__).resolve().parents[2]
W = Path(receipt["level1_K_source"]["path"]).parents[2]
O = options.output
O.mkdir(exist_ok=False)
sys.path.insert(0, str(GENERATOR_ROOT / "tools/block"))
from entry_formatter import (
    SourceComponents,
    SymbolicConditions,
    format_owned_entry_boundary,
)
from fractional_source import FractionalSourceArrays, array_declaration
from render_fp301_statements import render_entry_registers
from render_support import (
    component_source,
    definition_introduction_source,
    expression,
    identifier,
    unfold_declaration,
)
from forward_resources import load_resource_vocabulary
from symbolic_state import Expr
from resource_seed import load_public_seed, seed_owned_resources
from system_shape_seed import seed_system_shapes


def bind(p):
    p = Path(p)
    return {"path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}


forward = Path(receipt["source_pass"]["path"])
data = json.loads(forward.read_text())
vpath = Path(receipt["vocabulary"]["path"])
vocabulary = load_resource_vocabulary(vpath, bind(vpath)["sha256"])
array = array_declaration(vocabulary)
shapes = json.loads(Path(receipt["system_shapes"]["path"]).read_text())["rows"]
system_binders = [
    {"name": Expr.from_dict(row["symbol"]).value, "type": "bv " + str(row["width"])}
    for row in shapes
    if row["shape"] in ("mask", "bits")
]
seedpath = Path(seed_manifest["seed"]["path"])
public_seed = load_public_seed(seedpath, bind(seedpath)["sha256"])
domain = json.loads(Path(seed_manifest["domain"]["path"]).read_text())
owned = seed_owned_resources(
    public_seed,
    entry_pc=int(public_seed["entry_pc"], 0),
    vocabulary=vocabulary,
    constants=domain["constants"],
    facts=domain["projection"]["facts"],
)
owned.state = seed_system_shapes(
    owned.state, shapes, collection_ownership_id="resource_0"
).state
terminal_ids = [
    row["id"] for row in owned.ownership["components"] if row["source"] == "True"
]
assert len(terminal_ids) == 1
continuation = {
    "name": "K",
    "coq": "K",
    "source_binding": {
        "source": str(W / "ZesuSsz/Contracts/Level1.v") + "#IslarisContractSpec"
    },
    "terminal_id": terminal_ids[0],
}
pilots = [
    "6960",
    "6974",
    "697c",
    "69a4",
    "69b0",
    "69d8",
    "69e0",
    "69e8",
    "6a00",
    "6a08",
    "6a14",
    "6a64",
    "6a6c",
    "6a78",
    "6aa8",
    "6ab4",
    "698c",
    "6a24",
    "6ac4",
    "6ae0",
]
cases = []
emitted = []
header = """(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Export ZesuSsz.Contracts.DecodeItemDomainRanges.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
"""
# These are the source-bound argument and continuation types from Level 1.
base_telescope = (
    " `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z)"
)
base_arguments = ["args", "returnAddress"]
allowed_helpers = {
    row["helper"]["owner"] + "." + row["helper"]["name"] for row in vocabulary["rows"]
}

for suffix in pilots:
    pc = "0x800d" + suffix
    index = next(i for i, b in enumerate(data["boundaries"]) if b["pc"] == pc)
    if suffix in {"6a24", "6ac4"}:
        from render_fp301_statements import render_loop_head
        directory = O / "sources/ZesuSsz/Generated/DecodeItem/FP301"
        directory.mkdir(parents=True, exist_ok=True)
        outputs = []
        for structural in [False, True]:
            file = directory / ("Pilot" + suffix + ("Structural" if structural else "Entries") + ".v")
            file.write_text(render_loop_head(suffix, header, structural))
            outputs.append(bind(file))
        emitted.extend(outputs)
        cases.append({"pc": pc, "status": "source_declarations_rendered",
                      "entry": outputs[0], "structural": outputs[1],
                      "qualified_entry": "ZesuSsz.Generated.DecodeItem.FP301.Pilot" + suffix + "Entries.fp_machineAt" + suffix,
                      "source_boundary": "tools/block/fixtures/fp301-loop-heads.json#" + suffix,
                      "definition_count": 5, "proof_ran": False})
        continue
    boundary = deepcopy(data["boundaries"][index])
    name = "fp_machineAt" + suffix
    name = identifier(name, "generated entry")
    source_ref = str(forward) + "#/boundaries/" + str(index)

    def provenance(*args, **kwargs):
        return {"source": source_ref}

    # Frame exactly the existing Level1 exit continuation outside every alternative.
    for alternative in boundary["alternatives"]:
        resource = alternative["resource_boundary"]
        for component in resource["components"]:
            if component["source"] == "⌜domain args⌝":
                component["source"] = (
                    "⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args⌝"
                )
    plain = SourceComponents(
        {"K": {"owner": "parameter", "name": "K"}},
        continuation_id="level1_K",
        provenance=provenance,
    )
    components = FractionalSourceArrays(plain, declaration=array)
    conditions = SymbolicConditions(provenance)
    formatted = format_owned_entry_boundary(
        boundary,
        original_seed=owned,
        vocabulary=vocabulary,
        continuation=continuation,
        join_options={"outer_names": base_arguments},
        case_id=pc,
        source_policy="source-only",
        handwritten_owner="Level1.IslarisContractSpec",
        continuation_id="level1_K",
        guard_scope=(0,),
        component_adapter=components,
        condition_adapter=conditions,
        helper_arguments=lambda body, context: list(base_arguments),
        scoped_binders=system_binders,
    )
    record = {
        "pc": pc,
        "source_boundary": source_ref,
        "alternative_count": len(boundary["alternatives"]),
        "status": formatted.status,
        "manifest": formatted.manifest,
        "reports": formatted.reports,
        "guard_normalizations": conditions.normalizations,
        "fraction_applications": components.applications,
        "proof_ran": False,
    }
    if formatted.response is None:
        cases.append(record)
        continue
    helpers = {
        row["suffix"]: name + "_" + row["suffix"]
        for row in formatted.response["body"]["additional_definitions"]
    }
    facts = []

    def render(node):
        kind = node["kind"]
        if kind in ("application", "continuation"):
            reference = node["predicate"]
            arguments = node["arguments"]
            if set(reference) == {"suffix"}:
                target = helpers[reference["suffix"]]
            elif reference == {"owner": "parameter", "name": "K"}:
                if kind != "continuation" or arguments:
                    raise ValueError(
                        "The Level1 K parameter is applied or reinterpreted."
                    )
                return "K"
            else:
                target = reference["owner"] + "." + reference["name"]
                if target not in allowed_helpers:
                    raise ValueError(
                        "An application lacks a source-bound helper: " + target
                    )
            return target + "".join(
                " (" + expression(argument, "application argument") + ")"
                for argument in arguments
            )
        if kind == "pure":
            terms = []
            for term in node["terms"]:
                value = expression(term["term"]["value"], "source-derived pure term")
                terms.append("(" + value + ")")
                facts.append(
                    {"term": value, "provenance": deepcopy(term["provenance"])}
                )
            return "⌜" + " /\\ ".join(terms) + "⌝"
        if kind == "disjunction":
            return (
                "("
                + " ∨ ".join("(" + render(alt) + ")" for alt in node["alternatives"])
                + ")"
            )
        return component_source(node, {}, {"source_hashes": {}}, W, None)

    def body_source(body):
        if body.get("lets") or body.get("loop"):
            raise ValueError("This source adapter has no let/loop declaration binding.")
        result = (
            "("
            + " ∗ ".join(render(component) for component in body["components"])
            + ")"
        )
        if body["existentials"]:
            telescope = " ".join(
                "("
                + identifier(binder["name"], "source existential")
                + " : "
                + expression(binder["type"], "source type")
                + ")"
                for binder in body["existentials"]
            )
            result = "(∃ " + telescope + ", " + result + ")"
        return result

    definitions = []
    for helper in formatted.response["body"]["additional_definitions"]:
        assert not next(
            row
            for row in formatted.manifest["helpers"]
            if row["suffix"] == helper["suffix"]
        )["outer_binders"]
        definition = (
            "Definition "
            + helpers[helper["suffix"]]
            + base_telescope
            + " : iProp Sigma := "
            + body_source(helper["body"])
            + "%I.\n"
        )
        definition = render_entry_registers(definition)
        definition_introduction_source(definition, helpers[helper["suffix"]])
        definitions.append((helpers[helper["suffix"]], definition))
    definition = (
        "Definition "
        + name
        + base_telescope
        + " (K : iProp Sigma) : iProp Sigma := "
        + body_source(formatted.response["body"])
        + "%I.\n"
    )
    definition_introduction_source(definition, name)
    definitions.append((name, definition))
    module = "Pilot" + suffix + "Entries"
    relative = Path("ZesuSsz/Generated/DecodeItem/FP301")
    directory = O / "sources" / relative
    directory.mkdir(parents=True, exist_ok=True)
    entry = directory / (module + ".v")
    entry.write_text(header + "\n".join(definition for _, definition in definitions))
    structural = directory / ("Pilot" + suffix + "Structural.v")
    source = header + "Require Import " + ".".join((relative / module).parts) + ".\n"
    for symbol, definition in definitions:
        source += (
            unfold_declaration(
                symbol, instance_name=symbol + "_unfold", locality="export"
            )
            + definition_introduction_source(definition, symbol)
            + "\n"
        )
    structural.write_text(source)
    for file in [entry, structural]:
        text = file.read_text()
        assert not re.search(r"\b(?:Proof|Qed|Admitted|Axiom|Ltac|Ltac2)\b", text)
    record.update(
        status="source_declarations_rendered",
        entry=bind(entry),
        structural=bind(structural),
        qualified_entry=".".join((relative / module).parts) + "." + name,
        definition_count=len(definitions),
        facts=facts,
        response=formatted.response,
        physical_declaration_check="pending",
        byte_identity_with_OLD="not_assumed",
    )
    emitted.extend([bind(entry), bind(structural)])
    cases.append(record)

(O / "RESULT.json").write_text(
    json.dumps(
        {
            "status": "SOURCE_DECLARATIONS_ONLY",
            "input_receipt": bind(options.input_receipt),
            "seed_manifest": bind(options.seed_manifest),
            "source_pass": bind(forward),
            "formatter_sources": [
                bind(GENERATOR_ROOT / "tools/block" / name)
                for name in [
                    "entry_formatter.py",
                    "join_generalize.py",
                    "join_refutations.py",
                    "guard_normal_form.py",
                    "coq_scopes.py",
                    "fractional_source.py",
                    "render_support.py",
                    "render_fp301_entries.py",
                ]
            ],
            "level1_K_source": bind(W / "ZesuSsz/Contracts/Level1.v"),
            "vocabulary": bind(vpath),
            "system_shapes": bind(Path(receipt["system_shapes"]["path"])),
            "cases": cases,
            "rendered_count": sum(
                c["status"] == "source_declarations_rendered" for c in cases
            ),
            "refused_count": sum(
                c["status"] != "source_declarations_rendered" for c in cases
            ),
            "sources": emitted,
            "proof_scripts_emitted": False,
            "new_native_calls": 0,
            "native_release": False,
            "join_seeds_added": True,
        },
        indent=2,
    )
    + "\n"
)
print(
    json.dumps(
        {
            "rendered": sum(
                c["status"] == "source_declarations_rendered" for c in cases
            ),
            "refused": [
                (c["pc"], c["reports"])
                for c in cases
                if c["status"] != "source_declarations_rendered"
            ],
            "result": bind(O / "RESULT.json"),
        }
    )
)
