"""Render declarations only from frozen source-pass alternatives and Level 1 framing."""

from copy import deepcopy
from pathlib import Path
import argparse, hashlib, json, os, re, sys

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
parser.add_argument("--loop-heads", type=Path, default=None,
                    help="loop-head file of this render (default: the profile's committed fixture)")
parser.add_argument("--backward-pins", type=Path, default=None,
                    help="(second pass, set by this script) BACKWARD-PINS.json of the first pass")
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
# Second and later passes: the pins `entry_hist.backward_pins` computed on the previous pass's entries.
previous_pass = json.loads(options.backward_pins.read_text()) if options.backward_pins else {"pass": 0, "pins": {}}
backward_pins = previous_pass["pins"]
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
from join_generalize import drop_entry_resources
from resource_seed import load_public_seed, seed_owned_resources
from system_shape_seed import seed_system_shapes
from function_profiles import (add_return_alignment, function_returns, load_profile, pilot_header, return_case,
                               return_sites)
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
# Hidden history (`entry_hist`) and per-slot frame cells (`frame_slots`): profile keys.
import entry_hist
entry_hist.configure(load_profile(options.function))
slot_table = slot_regions = None
if entry_hist.FRAME_SLOTS:
    slot_table = entry_hist.frame_slot_table(data, lambda value: Expr.from_dict(value).coq())
    slot_regions = entry_hist.region_offsets(data)
    entry_hist.SLOT_TABLE, entry_hist.SLOT_REGIONS = slot_table, slot_regions
# The call plans of the forward pass (JOINS.json `calls`) and the block starts: at a call block and
# at a return site the last call's record and its named registers stay visible.
call_plans = (json.loads((forward.parent / "JOINS.json").read_text()).get("calls", {})
              if (forward.parent / "JOINS.json").exists() else {})
block_starts = sorted(int(load_profile(options.function).pc(block), 0)
                      for block in load_profile(options.function)["blocks"])
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
entry_hist.CONSTANTS = domain["constants"]
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
parents, joins_record = {}, {}
if receipt.get("joins"):
    joins_record = json.loads(Path(receipt["joins"]["path"]).read_text())
    roots.update(joins_record.get("roots", {}))
    parents = joins_record.get("parents", {})
# Resource texts of a seed's root tree that a join `drop` row removed on the way to the seed: an
# entry rendered on that root from such a seed does not own them (join_generalize.inherited_drops).
seed_drops = joins_record.get("seed_drops", {})
# An edge into a mixed-root join may start at a join or loop-head seed: it lifts on the
# seed the source pass lifted it on.
lift_seeds = dict(root_seeds)
if receipt.get("join_seeds"):
    from join_generalize import seed_from_record
    seeds_path = Path(receipt["join_seeds"]["path"])
    if bind(seeds_path)["sha256"] != receipt["join_seeds"]["sha256"]:
        raise ValueError("A frozen renderer source changed: " + str(seeds_path))
    for pc, row in json.loads(seeds_path.read_text())["seeds"].items():
        lift_seeds[pc] = seed_from_record(row)
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
sites = dict(("Return" + suffix, design) for suffix, design in return_sites(profile))
# A tail call's callee returns to the function's return address: its package is the state
# the function exits with on that path (the source pass's `tail_returns`).
tails = {"ReturnTail" + profile.key(call["call_site_pc"]): call for call in profile.get("tail_calls", [])}
pilots.extend(sites)
pilots.extend(tails)
if sites:
    # Every return exit belongs to a design row; a site without an exit is reported.
    from return_exit import match_return_exits
    _, unreached_sites = match_return_exits(function_returns(profile),
                                            [row for row in data["exits"] if row["kind"] == "function_return"])
loop_heads = set(profile["loop_heads"])
cases = []
emitted = []
header = pilot_header(profile)
# A charged profile: every block entry owns `step_budget (B)`, B from tools/block/budgets.py (BUDGETS.json
# beside RESULT.json); a return package and an unreachable entry own none.
budget_record = None
if profile.charged:
    import budgets
    budget_record = budgets.entry_budgets(profile)
    (O / "BUDGETS.json").write_text(json.dumps(budget_record, indent=1) + "\n")
# These are the source-bound argument and continuation types from Level 1.
base_telescope = profile.telescope()
base_arguments = ["args", "returnAddress"]
# An opaque contract predicate that an annotation row binds (profile `opaque_predicates`, compiled by
# tools/oblig/annotations.py) renders as its qualified name; no other opaque predicate has an owner.
opaque_predicates = {name: {"owner": row["owner"], "name": row["name"]}
                     for name, row in profile.get("opaque_predicates", {}).items()}
allowed_helpers = {
    row["helper"]["owner"] + "." + row["helper"]["name"] for row in vocabulary["rows"]
} | {row["owner"] + "." + row["name"] for row in opaque_predicates.values()}
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
# A join history (`zesu_join_history`) is a Hist definition: the unsealed text needs the library too.
check = RocqContradictionCheck(
    json.loads(options.coqc_args.read_text()), header + entry_hist.HIST_LIBRARY,
    O / "contradiction-checks",
    profile.args_type,
)
if options.backward_pins is not None:
    # The unsealed definitions do not depend on the pins: the previous pass's checks stand.
    check.checked.extend((frozenset(map(tuple, key)), path) for key, path
                         in json.loads((options.backward_pins.parent / "CHECKED.json").read_text()))

def return_boundary(designs, slot=None):
    """The function_return exits as alternatives, each with its design's return fact.

    Each design row names its return instruction; every exit at that instruction
    is one alternative. An exit renders on its seed's root tree (as a single join
    edge does: the seed join's history design facts (`zesu_join_history`, the reason
    an error join holds) stay, so a package states why the join it continues from
    was reached), and a return fact is a pure component of that scope.
    `{bytes@ADDR}` names the exit value of the owned array at ADDR. A return fact
    `True` allows the exit resources only: no component is added. A return block with
    entry slots (a duplicated return join) gives one package per slot: `slot` keeps the
    exits that continue from that slot."""
    from join_generalize import align_join_edges
    from forward_resources import _strip_enclosure
    from return_exit import allows_exit_resources_only, exit_slot, match_return_exits, return_block_slots
    # A design that no path reaches renders no alternative; its blocks do not render either.
    at = {int(design["return_instruction_pc"], 0) for design in designs}
    pairs, unreached = match_return_exits(designs, [row for row in data["exits"] if row["kind"] == "function_return"
                                                    and int(row["instruction_pc"], 0) in at])
    if slot is not None:
        block = return_block_slots(data["boundaries"], [exit for _, exit in pairs])
        pairs = [(design, exit) for design, exit in pairs if exit_slot(block, exit) == slot]
    if not pairs:
        raise ValueError("The return package has no function_return exit.")
    alternatives = []
    for design, exit in pairs:
        alternative = {"predecessor_pc": exit["block_pc"], "seed_pc": exit["seed_pc"], "state": exit["state"],
                       "path": exit["path"], "back_edge": False,
                       "resource_boundary": deepcopy(exit["resource_boundary"])}
        # The exit renders on its seed's root tree without the resources a join drop row removed
        # on the way to that seed.
        root, (alternative,) = drop_entry_resources(
            root_seeds[roots.get(exit["seed_pc"], public_seed["entry_pc"])], [alternative], [], seed_drops)
        terminal = next(row["id"] for row in root.ownership["components"] if row["source"] == "True")
        alternative, = align_join_edges([alternative], root.ownership, terminal, "K", keep_binders=True,
                                        keep_designs=lambda source: entry_hist.is_join_history(
                                            source.strip().removeprefix("⌜").removesuffix("⌝")))[0]
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


def return_pc(suffix):
    """The case name of a return package pilot."""
    return return_case(suffix[len("Return"):])

def slot_block(suffix):
    """The boundary whose entry slots `suffix` renders one entry each for, or None: a slot
    block's own boundary; for a return site, its return block when that block carries slots
    (one return package per slot, each with its incoming edge's exit state)."""
    if suffix in tails:
        return None
    if suffix in sites:
        from return_exit import return_block_slots
        at = int(sites[suffix]["return_instruction_pc"], 0)
        return return_block_slots(data["boundaries"], [row for row in data["exits"] if row["kind"] == "function_return"
                                                       and int(row["instruction_pc"], 0) == at])
    block = next(b for b in data["boundaries"] if b["pc"] == profile.pc(suffix))
    return block if block.get("slots") else None


def entry_units(suffix):
    """(suffix, slot) per rendered entry: one per entry slot of a slot block, else one."""
    block = slot_block(suffix)
    if block is not None:
        return [(suffix, slot) for slot in range(len(block["slots"]))]
    return [(suffix, None)]


units = [unit for suffix in pilots for unit in entry_units(suffix)]
module_definitions = {}
module_requires_of = {}   # stem -> the `entry_facts` imports of its module
from return_exit import add_entry_facts
for suffix, slot in units:
    if suffix in tails:
        pc = return_pc(suffix)
        index = None
        tail_return = next((row for row in data.get("tail_returns", [])
                            if row["call_site_pc"] == tails[suffix]["call_site_pc"]), None)
        if tail_return is None:
            cases.append({"pc": pc, "status": "refused_no_tail_return", "proof_ran": False,
                          "reports": [{"kind": "no_tail_return_seed",
                                       "detail": joins_record.get("refusals", {}).get(
                                           tails[suffix]["call_site_pc"], "no tail-call exit")}]})
            continue
    elif suffix in sites:
        pc = return_pc(suffix)
        index = None
        if sites[suffix]["return_instruction_pc"] in unreached_sites:
            cases.append({"pc": pc, "status": "refused_unreached_return_site", "proof_ran": False,
                          "reports": [{"kind": "unreached_return_site",
                                       "detail": sites[suffix]["return_instruction_pc"]}]})
            continue
    else:
        pc = profile.pc(suffix)
        index = next(i for i, b in enumerate(data["boundaries"]) if b["pc"] == pc)
    # The entry's step budget (a charged profile): a block entry's own; none for a return package.
    entry_budget = (budgets.budget_text(budget_record, suffix)
                    if budget_record is not None and index is not None else None)
    if suffix in loop_heads:
        from render_fp301_statements import render_loop_head
        directory = O / "sources" / profile.generated_directory
        directory.mkdir(parents=True, exist_ok=True)
        outputs = []
        try:
            texts = [render_loop_head(suffix, header, structural, profile, options.loop_heads,
                                      **({"budget": entry_budget} if entry_budget is not None else {}))
                     for structural in [False, True]]
        except (FileNotFoundError, ValueError) as error:
            # The pass produced no loop-head row (its entry edge is incomplete or refused).
            cases.append({"pc": pc, "status": "refused_no_loop_head_row", "proof_ran": False,
                          "reports": [{"kind": "no_loop_head_row", "detail": str(error)}]})
            continue
        for structural, text in zip([False, True], texts):
            file = directory / ("Pilot" + suffix + ("Structural" if structural else "Entries") + ".v")
            file.write_text(text)
            outputs.append(bind(file))
        emitted.extend(outputs)
        cases.append({"pc": pc, "status": "source_declarations_rendered",
                      "entry": outputs[0], "structural": outputs[1],
                      "qualified_entry": profile.qualified("Pilot" + suffix + "Entries", "fp_machineAt" + suffix),
                      "source_boundary": profile["loop_head_fixture"] + "#" + suffix,
                      "definition_count": (directory / ("Pilot" + suffix + "Entries.v")).read_text().count("\nDefinition "),
                      **({"hist": {key: value for key, value in __import__("render_fp301_statements").LOOP_HIST_META.items()
                                   if key.startswith("fp_machineAt" + suffix + "_")}}
                         if __import__("render_fp301_statements").LOOP_HIST_META else {}),
                      "proof_ran": False})
        continue
    if suffix in guard_refusals:
        cases.append({"pc": pc, "status": "refused_incomplete_boundary",
                      "reports": [{"kind": "reaching_stop_guard", "detail": guard_refusals[suffix]}],
                      "proof_ran": False})
        continue
    if suffix in tails:
        # The tail return renders from its seed alternative, as a call-return site does.
        boundary = {"pc": pc, "status": "generated", "alternatives": deepcopy(tail_return["alternatives"]),
                    "reaching_stops": []}
    else:
        boundary = (return_boundary([sites[suffix]], slot) if suffix in sites
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
    package = suffix in sites or suffix in tails
    if slot is not None and not package:
        # An entry slot renders the alternatives of its own incoming edge only.
        boundary["alternatives"] = [boundary["alternatives"][number]
                                    for number in boundary["slots"][slot]["alternatives"]]
    unreachable = suffix in profile.get("unreachable_entries", [])
    if unreachable and suffix in profile.get("unreachable_reached", []) and boundary["alternatives"] \
            and all(row["predecessor_pc"] is None for row in boundary["alternatives"]):
        # A `reached: contradictory_guards` row cut every edge from a predecessor block; what remains is
        # the block's own seed (a call return site), rendered as usual. Each cut edge's predecessor still
        # steps into this entry and must close by contradiction in the kernel.
        unreachable = False
    if unreachable and boundary["alternatives"]:
        # An `unreachable` annotation row at a block the forward pass reaches is wrong.
        cases.append({"pc": pc, "status": "refused_unreachable_row", "proof_ran": False,
                      "reports": [{"kind": "unreachable_row_reached",
                                   "detail": "an unreachable annotation row names a block the pass reaches"}]})
        continue
    if not boundary["alternatives"] and unreachable and slot is None and not package:
        # The annotation row states that no path reaches the block: its entry is ⌜False⌝, and the
        # step of each predecessor into it must close by contradiction in the kernel.
        name = "fp_machineAt" + suffix
        directory = O / "sources" / profile.generated_directory
        directory.mkdir(parents=True, exist_ok=True)
        entries = directory / ("Pilot" + suffix + "Entries.v")
        structural = directory / ("Pilot" + suffix + "Structural.v")
        entries.write_text(header + "Definition %s `{!islaG Sigma} `{!threadG} (args : %s) (returnAddress : Z) "
                           "(K : iProp Sigma) : iProp Sigma := ⌜False⌝%%I.\n" % (name, profile.args_type))
        structural.write_text(header + "Require Import %s.\n#[export] Instance %s_unfold : LithiumUnfold (@%s) := I.\n"
                              "#[export] Typeclasses Opaque %s.\n"
                              % (profile.qualified("Pilot" + suffix + "Entries"), name, name, name))
        emitted.extend([bind(entries), bind(structural)])
        cases.append({"pc": pc, "status": "source_declarations_rendered", "entry": bind(entries),
                      "structural": bind(structural),
                      "qualified_entry": profile.qualified("Pilot" + suffix + "Entries", name),
                      "source_boundary": "annotation:unreachable#" + suffix, "definition_count": 1,
                      "unreachable": True})
        continue
    if not boundary["alternatives"]:
        # No path reaches the block and no stop does either: nothing to render or lift.
        cases.append({"pc": pc, "status": "refused_no_alternatives", "proof_ran": False,
                      "reports": [{"kind": "unreached_boundary",
                                   "detail": "the boundary has no alternative and no reaching stop"}]})
        continue
    # A seed without a recorded root (a join seed of an older pass) shares the entry tree.
    origin_roots = {roots.get(alternative["seed_pc"], public_seed["entry_pc"])
                    for alternative in boundary["alternatives"]}
    lifted_binders = []
    if None in origin_roots:
        cases.append({"pc": pc, "status": "refused_mixed_roots", "roots": sorted(map(str, origin_roots)),
                      "proof_ran": False})
        continue
    if len(origin_roots) != 1:
        # Edges from different call-return roots render on their deepest common ancestor.
        from join_generalize import common_root_ancestor, lift_call_return_edges
        ancestor = common_root_ancestor(sorted(origin_roots), parents)
        try:
            if ancestor is None:
                raise ValueError("no common ancestor")
            drops = [{"root": profile.pc(item["root"]), "resources": item["resources"]}
                     for item in profile.get("join_drops", {}).get(suffix, [])]
            boundary["alternatives"], lifted_binders = lift_call_return_edges(
                boundary["alternatives"], seeds=lift_seeds, roots=roots, ancestor=ancestor, vocabulary=vocabulary,
                drops=drops)
        except ValueError as error:
            cases.append({"pc": pc, "status": "refused_mixed_roots", "roots": sorted(map(str, origin_roots)),
                          "reports": [{"kind": "join_lift_refused", "detail": str(error)}], "proof_ran": False})
            continue
        origin_roots = {ancestor}
    origin_root = origin_roots.pop()
    # A join drop row whose root is the seed the entry renders on, and the drops inherited by the
    # edges' seeds: the entry does not own those resources, and an edge that holds them leaves them.
    try:
        original_seed, boundary["alternatives"] = drop_entry_resources(
            root_seeds[origin_root], boundary["alternatives"],
            [text for item in profile.get("join_drops", {}).get(suffix, [])
             if profile.pc(item["root"]) == origin_root for text in item["resources"]], seed_drops)
    except ValueError as error:
        cases.append({"pc": pc, "status": "refused_join_drop", "proof_ran": False,
                      "reports": [{"kind": "join_drop_refused", "detail": str(error)}]})
        continue
    name = ("fp_machine" + suffix if package else "fp_machineAt" + suffix) + ("" if slot is None else "_slot" + str(slot))
    name = identifier(name, "generated entry")
    source_ref = str(forward) + ("#/tail_returns" if suffix in tails else "#/exits" if index is None
                                 else "#/boundaries/" + str(index))
    join_design = [entry_hist.design_fact_text(row) for row in profile.get("join_designs", {}).get(suffix, [])]
    join_frames = profile.get("join_frames", {}).get(suffix, [])

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
            {"K": {"owner": "parameter", "name": "K"}, **opaque_predicates},
            continuation_id="level1_K",
            provenance=provenance,
        )
        components = FractionalSourceArrays(plain, declaration=array,
                                            seal_owned=entry_hist.ARRAY_SPELLING == 'sealed')
        conditions = SymbolicConditions(provenance)
        formatted = format_owned_entry_boundary(
            boundary,
            original_seed=original_seed,
            vocabulary=vocabulary,
            continuation=continuation,
            join_options={"outer_names": base_arguments, "design_facts": join_design,
                          "live_registers": data.get("liveness", {}).get(pc), "lifted_binders": lifted_binders,
                          "frame_writes": entry_hist.frame_writes(join_frames, data) if join_frames else ()},
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
        # With per-slot frame cells a word loaded from a slot is the cell's word (entry_hist).
        word_fold = entry_hist.fold_literal_words if entry_hist.FRAME_SLOTS else (lambda text: text)

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
                    value = word_fold(expression(term["term"]["value"], "source-derived pure term"))
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

        def body_source(body, seal_as=None, budget=None):
            if body.get("lets") or body.get("loop"):
                raise ValueError("This source adapter has no let/loop declaration binding.")
            rendered_components, slot_binders = [], []
            taken = {binder["name"] for binder in body["existentials"]}
            for component in body["components"]:
                text = render(component)
                split = None
                if entry_hist.FRAME_SLOTS and component["kind"] in ("byte_array", "unknown_byte_array"):
                    # One cell per saved-register slot, at the store's address form.
                    split = entry_hist.slot_components(
                        component["kind"], component["address"],
                        component["value" if component["kind"] == "byte_array" else "length"],
                        slot_table, slot_regions, taken)
                if split is None:
                    rendered_components.append((component, word_fold(text)))
                else:
                    rendered_components.extend((component, word_fold(piece)) for piece in split[0])
                    slot_binders.extend(split[1])
                    slot_reports.append({"address": component["address"], "pieces": len(split[0]),
                                         "binders": [binder["name"] for binder in split[1]]})
            if budget is not None:
                # The step budget, its `{reg:xR}` read in this alternative, among the owned resources.
                conjunct = budgets.budget_conjunct(
                    budgets.resolve_registers(budget, [text for _, text in rendered_components]))
                rendered_components.insert(budgets.place_budget([component["kind"] for component, _
                                                                 in rendered_components]),
                                           ({"kind": "step_budget"}, conjunct))
            body = {**body, "existentials": body["existentials"] + slot_binders}
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
            if seal_as is not None:
                # Ghost binders and hidden facts move into one history proposition.
                binders = [{"name": binder["name"], "type": expression(binder["type"], "source type")}
                           for binder in existentials]
                facts = [text[1:-1] for component, text in rendered_components if component["kind"] == "pure"]
                seal = entry_hist.seal_alternative(
                    seal_as, plain_telescope, plain_binders, binders,
                    [text for component, text in rendered_components if component["kind"] not in ("pure", "true")],
                    facts,
                    # The function return entry (`Return`) is no block: no call record of its own.
                    ((entry_hist.call_visible_patterns(profile.pc(block[0]), call_plans, block_starts, binders,
                                                      facts)
                      + entry_hist.loop_entry_patterns(
                          profile.pc(block[0]), {profile.pc(design['entry_predecessor'])
                                                 for design in profile.get('loop_designs', [])
                                                 if design.get('entry_predecessor')}, binders, facts))
                     if (block := re.match(r"[0-9a-f]+(?=_|$)", suffix)) else [])
                    # Profile `hist_pinned`: facts that stay visible and keep their binders live.
                    + profile.get("hist_pinned", []),
                    weak_patterns=profile.get("hist_visible", []),
                    # A successor's live binder without a resource takes its value from this entry.
                    pinned=backward_pins.get(pc, {}).get("pinned", []),
                    visible_texts=backward_pins.get(pc, {}).get("facts", []))
                if seal is not None:   # An empty history keeps the plain shape.
                    sealed[seal_as] = seal
                region = profile.get("compliance", {}).get("exit_result")
                if region and suffix in sites and seal is not None:
                    # A return package: its result bytes and exit meaning premise, as data.
                    declarations, sealed_body, meta = sealed[seal_as]
                    # A stored piece reads as the package's own resource states it (word_fold).
                    declarations.extend(entry_hist.result_declarations(
                        seal_as, plain_telescope, plain_binders, meta,
                        [(component["kind"], component["address"],
                          word_fold(component["value"]) if component["kind"] == "byte_array"
                          else component["length"])
                         for component, _ in rendered_components
                         if component["kind"] in ("byte_array", "unknown_byte_array")]
                        + [("byte_array",) + piece for _, text in rendered_components
                           if (piece := entry_hist.array_definition_piece(text))],
                        region))
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
        sealed, emit = {}, []
        plain_binders = [{"name": "args", "type": profile.args_type}, {"name": "returnAddress", "type": "Z"}]
        plain_telescope = " " + entry_hist.telescope(plain_binders)
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
                + body_source(helper["body"], seal_as=helpers[helper["suffix"]], budget=entry_budget)
                + "%I.\n"
            )
            definition = render_entry_registers(definition, profile.name)
            definition_introduction_source(definition, helpers[helper["suffix"]])
            definitions.append((helpers[helper["suffix"]], definition))
            if helpers[helper["suffix"]] in sealed:
                declarations, sealed_body, meta = sealed[helpers[helper["suffix"]]]
                sealed_definition = ("Definition " + helpers[helper["suffix"]] + base_telescope
                                     + " : iProp Sigma := " + sealed_body + "%I.\n")
                definition_introduction_source(sealed_definition, helpers[helper["suffix"]])
                emit.extend(declarations)
                emit.append((helpers[helper["suffix"]], sealed_definition, "entry"))
                hist_meta[helpers[helper["suffix"]]] = meta
            else:
                emit.append((helpers[helper["suffix"]], definition, "entry"))
        definition = (
            "Definition "
            + name
            + base_telescope
            + " (K : iProp Sigma) : iProp Sigma := "
            + body_source(formatted.response["body"],
                          budget=None if formatted.response["body"]["additional_definitions"] else entry_budget)
            + "%I.\n"
        )
        definition_introduction_source(definition, name)
        definitions.append((name, definition))
        emit.append((name, definition, "entry"))
        last_emit[:] = emit
        return record, definitions, facts

    # A generated cut whose generalization binds a register value: refute
    # each source alternative first, so an infeasible arm cannot widen it.
    last_emit, hist_meta, slot_reports = [], {}, []
    refused_sources, refused_names = [], []
    try:
        record, definitions, facts = rendered(boundary)
        cut = record["manifest"].get("cut_generalization", {})
        if (cut.get("kind") == "generalized_owned_cut" and cut["plan"]["binders"]
                and boundary["status"] == "generated"):
            refused_sources = contradictory_sources(
                boundary, lambda alone: rendered(alone)[1], check
            )
            if refused_sources:
                boundary = without_alternatives(boundary, refused_sources)
        while True:
            hist_meta.clear()
            del slot_reports[:]
            record, definitions, facts = rendered(boundary)
            if definitions is None:
                break
            refused = contradictory_alternatives(definitions, check)
            if not refused:
                break
            refused_names.extend(refused)
            boundary = without_alternatives(boundary, refused_alternative_indices(refused))
    except BoundaryRefused as error:
        # Every alternative proves False, or the contradiction check could not run: a refusal row.
        if not options.record_refusals:
            raise
        cases.append({"pc": pc, "status": "refused_boundary", "proof_ran": False,
                      "refused_alternatives": refused_names, "refused_source_alternatives": refused_sources,
                      "reports": [{"kind": "boundary_refused", "detail": str(error)[-2000:]}]})
        continue
    record["refused_alternatives"] = refused_names
    record["refused_source_alternatives"] = refused_sources
    if definitions is None:
        cases.append(record)
        continue
    stem = "Function" + suffix if package else "Pilot" + suffix
    module = stem + "Entries"
    relative = Path(profile.generated_directory)
    directory = O / "sources" / relative
    directory.mkdir(parents=True, exist_ok=True)
    entry = directory / (module + ".v")
    # The slots of one block share its module.
    written = module_definitions.setdefault(stem, [])
    # Profile `entry_facts`: design facts a named entry variant states after its own pure facts,
    # with the modules they need (decodeItem's accepted/rejected exits).
    entry_facts = profile.get("entry_facts", {})
    requires = []
    for symbol, definition, kind in last_emit:
        spec = entry_facts.get(symbol) if kind == "entry" else None
        if spec:
            definition = add_entry_facts(definition, spec["facts"])
            requires.extend(line + "\n" for line in spec.get("requires", []) if line + "\n" not in requires)
        written.append((symbol, definition, kind))
    module_requires = module_requires_of.setdefault(stem, [])
    module_requires.extend(line for line in requires if line not in module_requires)
    # Only a module that declares a history needs the history library.
    library = entry_hist.HIST_LIBRARY if any(kind == "hist" for _, _, kind in written) else ""
    library += "".join(module_requires)
    entry.write_text(header + library + "\n".join(definition for _, definition, _ in written))
    structural = directory / (stem + "Structural.v")
    source = (header + library
              + "Require Import " + ".".join((relative / module).parts) + ".\n")
    for symbol, definition, kind in written:
        if kind != "entry":
            # A history declaration gets opacity only: no unfold instance and no introduction.
            source += entry_hist.structural_opacity(symbol, kind)
            continue
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
    if hist_meta:
        record["hist"] = deepcopy(hist_meta)
    if slot_reports:
        record["frame_slots"] = list(slot_reports)
    record.update(
        status="source_declarations_rendered",
        entry=bind(entry),
        structural=bind(structural),
        qualified_entry=".".join((relative / module).parts) + "." + name,
        definition_count=len(written),
        facts=facts,
        physical_declaration_check="pending",
        byte_identity_with_OLD="not_assumed",
    )
    emitted.extend([bind(entry), bind(structural)])
    cases.append(record)

# A slot block's module grew after its earlier slots rendered: bind every case to its final files.
assert len(cases) == len(units)
for (suffix, slot), case in zip(units, cases):
    if slot is not None:
        boundary = slot_block(suffix)
        # A return package slot follows the same slot of its return block.
        case["slot"] = ({"index": slot, "predecessor_pc": boundary["pc"], "predecessor_slot": slot}
                        if suffix in sites else
                        {"index": slot, "predecessor_pc": boundary["slots"][slot]["predecessor_pc"],
                         "predecessor_slot": boundary["slots"][slot]["predecessor_slot"]})
        for key in ("entry", "structural"):
            if key in case:
                case[key] = bind(case[key]["path"])
if profile.get("return_package"):
    # A return-package design: one package every return block exits to (no forward-pass exit).
    from render_fp301_statements import render_return_package
    directory = O / "sources" / profile.generated_directory
    directory.mkdir(parents=True, exist_ok=True)
    files = []
    for kind, text in zip(("Entries", "Structural"), render_return_package(profile)):
        file = directory / ("FunctionReturn" + kind + ".v")
        file.write_text(text)
        files.append(bind(file))
    emitted.extend(files)
    cases.append({"pc": "function_return", "status": "source_declarations_rendered",
                  "entry": files[0], "structural": files[1],
                  "qualified_entry": profile.qualified("FunctionReturnEntries", "fp_machineReturn"),
                  "source_boundary": profile.path.name + "#return_package", "proof_ran": False})
emitted = list({row["path"]: bind(row["path"]) for row in emitted}.values())
# Every join keeps each pure fact of its edges, binds it in a history group, or drops it under a
# named rule (join_generalize.check_fact_accounting refuses a silent drop); the report lists the
# logged drops of each join.
join_accounting = {pc: plan.get("fact_accounting") for pc, plan in joins_record.get("plans", {}).items()}
unaccounted = sorted(pc for pc, row in join_accounting.items() if row is None)
assert not unaccounted, "joins without a fact accounting: " + ", ".join(unaccounted)

# A successor's live binder without a resource takes its value from the entry before it
# (`entry_hist.backward_pins`). When this pass's entries call for pins it did not render with,
# the next pass renders with them (this pass's output stays in `<output>-pass<n>`).
pin_variants = {}
for case in cases:
    for meta in case.get("hist", {}).values():
        if "hidden" in meta:
            pin_variants.setdefault(case["pc"], []).append(meta)
pin_edges = {(alternative["predecessor_pc"], boundary["pc"]) for boundary in data["boundaries"]
             for alternative in boundary["alternatives"] if alternative.get("predecessor_pc")}
for plan in call_plans.values():
    if plan["return_site_pc"] is not None:
        site = int(plan["call_site_pc"], 0)
        pin_edges.add((hex(max(start for start in block_starts if start <= site)), plan["return_site_pc"]))
witnessed = set()
if receipt.get("join_seeds"):
    for succ_pc, row in json.loads(seeds_path.read_text())["seeds"].items():
        for edge in row.get("join_edges", []):
            for witness in edge["ordered_witnesses"]:
                term = witness["expression"]
                if not (term.get("op") == "input" and term.get("value") == witness["binder"]):
                    witnessed.add((edge["predecessor_pc"], succ_pc, witness["binder"]))
pins = entry_hist.backward_pins(pin_variants, sorted(pin_edges), witnessed)
for pc, row in backward_pins.items():
    merged = pins.setdefault(pc, {"pinned": [], "facts": []})
    for key in ("pinned", "facts"):
        merged[key] = sorted(set(merged[key]) | set(row[key]))
pins = dict(sorted(pins.items()))
if pins != backward_pins:
    number = previous_pass["pass"] + 1
    assert number < 4, "the backward pins do not settle after three passes"
    (O / "BACKWARD-PINS.json").write_text(json.dumps({"pass": number, "pins": pins}, indent=1) + "\n")
    done = O.with_name(O.name + "-pass" + str(number))
    (O / "CHECKED.json").write_text(json.dumps([[sorted(map(list, key)), path.replace(str(O), str(done), 1)]
                                                for key, path in check.checked]))
    O.rename(done)
    arguments = sys.argv[1:]
    if "--backward-pins" in arguments:
        position = arguments.index("--backward-pins")
        del arguments[position:position + 2]
    sys.stdout.flush()
    os.execv(sys.executable, [sys.executable, sys.argv[0]] + arguments
             + ["--backward-pins", str(done / "BACKWARD-PINS.json")])

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
            "join_fact_accounting": join_accounting,
            "backward_pins": previous_pass,
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
                (c["pc"], c.get("reports", c["status"]))
                for c in cases
                if c["status"] != "source_declarations_rendered"
            ],
            "result": bind(O / "RESULT.json"),
        }
    )
)
