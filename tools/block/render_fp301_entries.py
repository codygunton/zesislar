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
parser.add_argument("--coqc-args", type=Path, required=True)
parser.add_argument("--function", default=None,
                    help="function profile name or path (default: decodeItem)")
parser.add_argument("--record-refusals", action="store_true",
                    help="record a guard-refused boundary and render the others")
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
from function_profiles import add_return_alignment, function_returns, load_profile, pilot_header
from boundary_guards import (
    BoundaryRefused,
    RocqContradictionCheck,
    contradictory_alternatives,
    contradictory_sources,
    refused_alternative_indices,
    require_complete_boundary,
    without_alternatives,
)


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
public_seed = add_return_alignment(load_public_seed(seedpath, bind(seedpath)["sha256"]),
                                   load_profile(options.function))
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
# A call's return site has its own seed: the root of the boundaries after it.
root_seeds = {public_seed["entry_pc"]: owned}
roots = {public_seed["entry_pc"]: public_seed["entry_pc"]}
if receipt.get("call_seeds"):
    from forward_resource_design import _state_from_result
    calls_path = Path(receipt["call_seeds"]["path"])
    if bind(calls_path)["sha256"] != receipt["call_seeds"]["sha256"]:
        raise ValueError("A frozen renderer source changed: " + str(calls_path))
    for site, row in json.loads(calls_path.read_text())["seeds"].items():
        call_seed = seed_owned_resources(
            row["public"], entry_pc=int(site, 0), vocabulary=vocabulary,
            constants=domain["constants"], facts=row["facts"])
        call_seed.state = _state_from_result(row["state"])
        root_seeds[site] = call_seed
if receipt.get("joins"):
    roots.update(json.loads(Path(receipt["joins"]["path"]).read_text()).get("roots", {}))
terminal_ids = [
    row["id"] for row in owned.ownership["components"] if row["source"] == "True"
]
source_binder_names = {binder["name"] for seed in root_seeds.values() for binder in seed.ownership["binders"]}
assert len(terminal_ids) == 1
continuation = {
    "name": "K",
    "coq": "K",
    "source_binding": {
        "source": str(W / "ZesuSsz/Contracts/Level1.v") + "#IslarisContractSpec"
    },
    "terminal_id": terminal_ids[0],
}
profile = load_profile(options.function)
pilots = list(profile["blocks"])
blocks = list(pilots)
# A function-return design adds the return package as one more rendered entry.
if function_returns(profile):
    pilots.append("Return")
loop_heads = set(profile["loop_heads"])
cases = []
emitted = []
header = pilot_header(profile)
# These are the source-bound argument and continuation types from Level 1.
base_telescope = profile.telescope()
base_arguments = ["args", "returnAddress"]
allowed_helpers = {
    row["helper"]["owner"] + "." + row["helper"]["name"] for row in vocabulary["rows"]
}
# Refuse every incomplete source boundary before any declaration renders.
guard_refusals = {}
for suffix in blocks:
    if suffix not in loop_heads:
        try:
            require_complete_boundary(
                next(b for b in data["boundaries"] if b["pc"] == profile.pc(suffix))
            )
        except BoundaryRefused as error:
            if not options.record_refusals:
                raise
            guard_refusals[suffix] = str(error)
check = RocqContradictionCheck(
    json.loads(options.coqc_args.read_text()), header, O / "contradiction-checks",
    profile.args_type,
)

def return_boundary(designs):
    """The function_return exits as alternatives, each with its design's return fact.

    Each design row names its return instruction; every exit at that instruction
    is one alternative. An exit renders on its seed's root tree (as a single join
    edge does), and a return fact is a pure component of that scope.
    `{bytes@ADDR}` names the exit value of the owned array at ADDR. A return fact
    `True` allows the exit resources only: no component is added."""
    from join_generalize import align_join_edges
    from forward_resources import _strip_enclosure
    from return_exit import allows_exit_resources_only, match_return_exits
    # A design that no path reaches renders no alternative; its blocks do not render either.
    pairs, unreached = match_return_exits(designs, [row for row in data["exits"] if row["kind"] == "function_return"])
    if not pairs:
        raise ValueError("The return package has no function_return exit.")
    alternatives = []
    for design, exit in pairs:
        alternative = {"predecessor_pc": exit["block_pc"], "seed_pc": exit["seed_pc"], "state": exit["state"],
                       "path": exit["path"], "back_edge": False,
                       "resource_boundary": deepcopy(exit["resource_boundary"])}
        root = root_seeds[roots.get(exit["seed_pc"], public_seed["entry_pc"])]
        terminal = next(row["id"] for row in root.ownership["components"] if row["source"] == "True")
        alternative, = align_join_edges([alternative], root.ownership, terminal, "K", keep_binders=True)[0]
        if allows_exit_resources_only(design):
            alternatives.append(alternative)
            continue
        fact = design["return_fact"]
        resource = alternative["resource_boundary"]
        values = {}
        for row in resource["components"]:
            match = re.fullmatch(r"(.*?)\s*↦ₘ(?:\{[^}]*\})?∗\s*(.*)", row["source"], re.S)
            if match:
                values[_strip_enclosure(match[1].strip())] = _strip_enclosure(match[2].strip())

        def array_value(match):
            if match[1] not in values:
                raise ValueError("The return design names no owned array at " + match[1])
            return values[match[1]]

        fact = re.sub(r"\{bytes@([^}]*)\}", array_value, fact)
        resource["components"].append({"id": "function_return_fact", "source": "⌜" + fact + "⌝",
                                       "provenance": {"function_return_design": design["return_fact"]}})
        tree = resource["tree"] if resource["tree"]["kind"] == "exists" else resource["tree"]["left"]
        tree["body"]["children"].append({"kind": "component", "id": "function_return_fact"})
        alternatives.append(alternative)
    return {"pc": "function_return", "status": "generated", "alternatives": alternatives,
            "reaching_stops": [], "unreached_return_sites": unreached}

for suffix in pilots:
    if suffix == "Return":
        pc = "function_return"
        index = None
    else:
        pc = profile.pc(suffix)
        index = next(i for i, b in enumerate(data["boundaries"]) if b["pc"] == pc)
    if suffix in loop_heads:
        from render_fp301_statements import render_loop_head
        directory = O / "sources" / profile.generated_directory
        directory.mkdir(parents=True, exist_ok=True)
        outputs = []
        for structural in [False, True]:
            file = directory / ("Pilot" + suffix + ("Structural" if structural else "Entries") + ".v")
            file.write_text(render_loop_head(suffix, header, structural, profile))
            outputs.append(bind(file))
        emitted.extend(outputs)
        cases.append({"pc": pc, "status": "source_declarations_rendered",
                      "entry": outputs[0], "structural": outputs[1],
                      "qualified_entry": profile.qualified("Pilot" + suffix + "Entries", "fp_machineAt" + suffix),
                      "source_boundary": profile["loop_head_fixture"] + "#" + suffix,
                      "definition_count": (directory / ("Pilot" + suffix + "Entries.v")).read_text().count("\nDefinition "),
                      "proof_ran": False})
        continue
    if suffix in guard_refusals:
        cases.append({"pc": pc, "status": "refused_incomplete_boundary",
                      "reports": [{"kind": "reaching_stop_guard", "detail": guard_refusals[suffix]}],
                      "proof_ran": False})
        continue
    boundary = (return_boundary(function_returns(profile)) if suffix == "Return"
                else deepcopy(data["boundaries"][index]))
    if boundary["status"] == "generated_call_return":
        # A return site renders from its call-return seed alternative.
        boundary["status"] = "generated"
    elif boundary["status"] in ("generated_join", "generated_loop_head"):
        # A seeded cut renders from its incoming edges, as an unseeded cut does;
        # its own seed alternative is the generalization of those same edges.
        boundary["alternatives"] = [
            alternative for alternative in boundary["alternatives"]
            if alternative["predecessor_pc"] is not None
        ]
        boundary["status"] = "handwritten_cut"
    # A seed without a recorded root (a join seed of an older pass) shares the entry tree.
    origin_roots = {roots.get(alternative["seed_pc"], public_seed["entry_pc"])
                    for alternative in boundary["alternatives"]}
    if len(origin_roots) != 1 or None in origin_roots:
        cases.append({"pc": pc, "status": "refused_mixed_roots", "roots": sorted(map(str, origin_roots)),
                      "proof_ran": False})
        continue
    original_seed = root_seeds[origin_roots.pop()]
    name = "fp_machineReturn" if suffix == "Return" else "fp_machineAt" + suffix
    name = identifier(name, "generated entry")
    source_ref = str(forward) + ("#/exits" if index is None else "#/boundaries/" + str(index))
    join_design = profile.get("join_designs", {}).get(suffix, [])

    def provenance(*args, **kwargs):
        return {"source": source_ref}

    # Frame exactly the existing Level1 exit continuation outside every alternative.
    for alternative in boundary["alternatives"]:
        resource = alternative["resource_boundary"]
        for component in resource["components"]:
            if component["source"] == "⌜domain args⌝":
                component["source"] = profile["domain_component"]
        # A byte read at a symbolic index renders as its owned-array lookup, in
        # path conditions as in register values (render_resource_boundary).
        reads = {json.dumps(row["expression"], sort_keys=True): row["term"]
                 for row in resource.get("owned_read_renderings", [])}

        def owned_reads(value):
            if value.get("op") == "owned_array_byte":
                term = reads.get(json.dumps(value, sort_keys=True))
                if term is None:
                    raise ValueError("A symbolic byte read has no owned rendering.")
                return {"op": "input", "width": 8, "value": term}
            return {**value, "args": [owned_reads(arg) for arg in value["args"]]} if "args" in value else value

        if reads:
            resource["path_conditions"] = [owned_reads(row) for row in resource.get("path_conditions", [])]

    def rendered(boundary):
        plain = SourceComponents(
            {"K": {"owner": "parameter", "name": "K"}},
            continuation_id="level1_K",
            provenance=provenance,
        )
        components = FractionalSourceArrays(plain, declaration=array)
        conditions = SymbolicConditions(provenance)
        formatted = format_owned_entry_boundary(
            boundary,
            original_seed=original_seed,
            vocabulary=vocabulary,
            continuation=continuation,
            join_options={"outer_names": base_arguments, "design_facts": join_design},
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
            return record, None, []
        record["response"] = formatted.response
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
            rendered_components = [(component, render(component)) for component in body["components"]]
            result = "(" + " ∗ ".join(text for _, text in rendered_components) + ")"
            # A Level 1 entry witness whose register a path overwrote occurs
            # nowhere in the body; nothing could instantiate it, so it is dropped.
            # System-shape and condition witnesses are kept as before.
            existentials = [
                binder for binder in body["existentials"]
                if binder["name"] not in source_binder_names
                or re.search(r"(?<![\w'])" + re.escape(binder["name"]) + r"(?![\w'])",
                             re.sub(r'"[^"]*"', "", result))
            ]
            if existentials:
                telescope = " ".join(
                    "("
                    + identifier(binder["name"], "source existential")
                    + " : "
                    + expression(binder["type"], "source type")
                    + ")"
                    for binder in existentials
                )

                def mentions(text):
                    text = re.sub(r'"[^"]*"', "", text)
                    return any(re.search(r"(?<![\w'])" + re.escape(binder["name"]) + r"(?![\w'])", text)
                               for binder in existentials)

                owned = [text for component, text in rendered_components if component["kind"] != "pure"]
                if any(mentions(text) for text in owned):
                    return "(∃ " + telescope + ", " + result + ")"
                # No owned resource fixes a witness: keep the resources and the
                # witness-free facts outside, and scope the telescope over the
                # facts that use it (owned resources before pure meaning facts).
                outer = [text for component, text in rendered_components
                         if component["kind"] != "pure" or not mentions(text)]
                inner = [text for component, text in rendered_components
                         if component["kind"] == "pure" and mentions(text)] or ["True"]
                result = ("(" + " ∗ ".join(outer + ["(∃ " + telescope + ", (" + " ∗ ".join(inner) + "))"])
                          + ")")
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
        return record, definitions, facts

    # A generated cut whose generalization binds a register value: refute
    # each source alternative first, so an infeasible arm cannot widen it.
    record, definitions, facts = rendered(boundary)
    cut = record["manifest"].get("cut_generalization", {})
    refused_sources = []
    if (cut.get("kind") == "generalized_owned_cut" and cut["plan"]["binders"]
            and boundary["status"] == "generated"):
        refused_sources = contradictory_sources(
            boundary, lambda alone: rendered(alone)[1], check
        )
        if refused_sources:
            boundary = without_alternatives(boundary, refused_sources)
    refused_names = []
    while True:
        record, definitions, facts = rendered(boundary)
        if definitions is None:
            break
        refused = contradictory_alternatives(definitions, check)
        if not refused:
            break
        refused_names.extend(refused)
        boundary = without_alternatives(boundary, refused_alternative_indices(refused))
    record["refused_alternatives"] = refused_names
    record["refused_source_alternatives"] = refused_sources
    if definitions is None:
        cases.append(record)
        continue
    stem = "FunctionReturn" if suffix == "Return" else "Pilot" + suffix
    module = stem + "Entries"
    relative = Path(profile.generated_directory)
    directory = O / "sources" / relative
    directory.mkdir(parents=True, exist_ok=True)
    entry = directory / (module + ".v")
    entry.write_text(header + "\n".join(definition for _, definition in definitions))
    structural = directory / (stem + "Structural.v")
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
        physical_declaration_check="pending",
        byte_identity_with_OLD="not_assumed",
    )
    emitted.extend([bind(entry), bind(structural)])
    cases.append(record)

(O / "RESULT.json").write_text(
    json.dumps(
        {
            "status": "SOURCE_DECLARATIONS_ONLY",
            "function": profile.name,
            "function_profile": bind(profile.path),
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
                    "function_profiles.py",
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
            "contradiction_checks": check.runs,
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
