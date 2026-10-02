#!/usr/bin/env python3
"""Generate whole-block proofs from inferred states and the pinned CFG.

States are JSON records with entry, binders, coq, spatial, and imports.
The context field can replace coq and spatial in a reached probe record.
The arguments field names a state's application in its predecessor.
No missing resource or successor state is guessed.

Sources stay under Evidence/det/blocks. A guarded compile copies the
sources into Generated/WriteSuccess temporarily. Only a closed block
and its state dependencies remain there after --promote.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "det"))

import call_sites  # noqa: E402
import gen_boundary  # noqa: E402
import gen_segment  # noqa: E402

STAGING = Path("ZesuSsz/Evidence/det/blocks")
GENERATED = Path("ZesuSsz/Generated/WriteSuccess")
STATE_MODULE = "ZesuSsz.Generated.WriteSuccess.States"
BUILD_DIR = Path("_build/agents/writer-generator")


def address(value: str | int) -> int:
    return int(value, 0) if isinstance(value, str) else value


def read_states(path: Path) -> dict[int, dict]:
    """Read a JSON list, a leader map, or a directory of probe records."""
    files = sorted(path.glob("*.json*")) if path.is_dir() else [path]
    states = {}
    for source in files:
        raw = source.read_text()
        rows = ([json.loads(line) for line in raw.splitlines() if line.strip()]
                if source.suffix == ".jsonl" else json.loads(raw))
        if isinstance(rows, dict):
            rows = ([rows] if any(key in rows for key in
                                 ("entry", "state_entry", "context", "spatial")) else
                    [dict(row, entry=leader) for leader, row in rows.items()])
        for row in rows:
            leader = address(row.get("state_entry", row.get("exit")
                                     if "context" in row else row.get("entry")))
            if leader in states:
                raise ValueError(f"duplicate state at {hex(leader)}")
            if row.get("bind_entry_witnesses"):
                row["binders"], row["arguments"] = gen_boundary.entry_witness_binders(
                    row["binders"], row.get("coq", []),
                    row.get("local_sorts", row.get("sorts", {})))
            states[leader] = row
    return states


def add_stack_resources(state: dict, spatial: list[str]) -> list[str]:
    """Add the approved stack boundary with an explicit recorded bound."""
    if "stack_size" not in state:
        return spatial
    pointer = state.get("stack_pointer", "sp")
    has_exact = any(atom.startswith('"x2" ↦ᵣ') for atom in spatial)
    if not re.fullmatch(r"[A-Za-z_][\w']*", pointer) and not has_exact:
        raise ValueError("a stack expression requires exact x2 ownership")
    if (re.fullmatch(r"[A-Za-z_][\w']*", pointer)
            and pointer not in gen_boundary.explicit_arguments(state["binders"]).split()):
        arguments = state.get("arguments", gen_boundary.explicit_arguments(state["binders"]))
        state["binders"] += f" ({pointer} : bv 64)"
        state["arguments"] = (arguments + f" {pointer}").strip()
    exact = f'"x2" ↦ᵣ RVal_Bits (bv_to_bvn {pointer})'
    if not has_exact:
        spatial = [re.sub(r'\(KindReg "x2", BitsShape 64\);?\s*', '', atom)
                   for atom in spatial]
        spatial = [re.sub(r';\s*\]', ']', atom) for atom in spatial]
        spatial.append(exact)
    size = state["stack_size"]
    facts = [f'⌜(bv_unsigned {pointer} `mod` 16 = 0)%Z⌝',
             f'⌜(mapRamBase defaultMap <= bv_unsigned {pointer} - {size} /\\ '
             f'bv_unsigned {pointer} < machineRamEnd defaultMap)%Z⌝']
    return spatial + [fact for fact in facts if fact not in spatial]


def state_source(leader: int, state: dict) -> str:
    if state.get("outcome", "reached") != "reached":
        raise ValueError(f"state {hex(leader)} did not reach its boundary")
    if "context" in state:
        coq, _persistent, spatial = gen_boundary.sections(state["context"])
    else:
        coq, spatial = state.get("coq", []), state["spatial"]
    spatial = gen_boundary.normalize_temporaries(
        [atom for resource in spatial for atom in gen_boundary.spatial_atoms(resource)])
    spatial = add_stack_resources(state, spatial)
    if state.get("block_exit") is not None:
        spatial = gen_boundary.strip_internal_handoffs(
            spatial, leader, int(str(state["block_exit"]), 0))
    spatial = gen_boundary.preserve_register_precision(
        spatial, set(state.get("entry_unknown_registers", []))
        - ({"x2"} if "stack_size" in state else set()))
    deduplicated = gen_boundary.deduplicate_register_shapes(spatial)
    if deduplicated != spatial:
        state["deduplicated"] = True
    spatial = gen_boundary.complete_register_file(deduplicated)
    source = gen_boundary.boundary_source(
        state.get("name", f"State_{leader:x}"), state["binders"], coq, spatial,
        seal=len(spatial) > gen_boundary.RULE_20_CONJUNCTS,
        call_resources=True, sorts=state.get("local_sorts", state.get("sorts")),
        witnesses=state.get("witnesses"))
    imports = ["ZesuSsz.Automation.All", "ZesuSsz.Automation.SealedCoverage",
               "isla.riscv64.riscv64", *state.get("imports", [])]
    return ("(* Generated by tools/block/gen_block.py. Do not edit. *)\n"
            + "\n".join(f"Require Import {module}." for module in dict.fromkeys(imports))
            + "\n\n" + source)


def state_application(leader: int, state: dict) -> str:
    if state.get("outcome") == "unreachable-successor":
        return "False"
    args = state.get("arguments", gen_boundary.explicit_arguments(state["binders"]))
    return f"{state.get('name', f'State_{leader:x}')} {args}".strip()


def generate(block: dict, states: dict[int, dict]) -> tuple[str, str]:
    """Reuse segment generation with guarded successor premises."""
    leader, end = address(block["start"]), address(block["end"])
    successors = [address(value) for value in block["successors"]]
    needed = list(dict.fromkeys([leader, *successors]))
    missing = [hex(value) for value in needed if value not in states]
    if missing:
        raise ValueError("missing inferred states: " + ", ".join(missing))
    for value in needed:
        if states[value].get("outcome") != "unreachable-successor":
            state_source(value, states[value])
        elif value == leader:
            raise ValueError("an entry cannot be an unreachable successor")
    _premises, _modules, _unknown = call_sites.premises(leader, end, strict=True)
    spec = {"name": f"block_{leader:x}", "entry": hex(leader), "exit": hex(end),
            "binders": states[leader]["binders"],
            "imports": [states[value].get("state_module",
                        f"{STATE_MODULE}.{states[value].get('name', f'State_{value:x}')}")
                        for value in needed
                        if states[value].get("outcome") != "unreachable-successor"],
            "spec": state_application(leader, states[leader]),
            "successors": [{"address": hex(value),
                            "spec": state_application(value, states[value])}
                           for value in successors]}
    source, name = gen_segment.from_spec(
        spec, ["ZesuSsz.Automation.Sets.call"], strict=True)
    # The segment writer supplies the common statement and proof. The block
    # writer supplies the call rule set and any callee's local unfold instance.
    source = gen_segment.REQUIRED + "\n" + source.replace(
        "tools/det/gen_segment.py", "tools/block/gen_block.py")
    table = call_sites.contracts()
    targets = {target for site, (target, _) in call_sites.call_sites().items()
               if leader <= site < end}
    unfolds = list(dict.fromkeys(
        table[target]["name"] for target in sorted(targets)
        if table[target].get("local_unfold", False)))
    if unfolds:
        instances = "\n".join(f"#[local] Instance : LithiumUnfold (@{callee}) := I.\n"
                              f"#[local] Typeclasses Opaque {callee}."
                              for callee in unfolds)
        source = source.replace(f"Lemma {name}", instances + f"\n\nLemma {name}", 1)
    return source, name


def compile_module(block_path: Path, state_paths: list[Path], build_dir: Path,
                   seconds: int, promote: bool = False) -> dict:
    """Restore all previous files after failure or a preview compile."""
    sources = [(path, GENERATED / "States" / path.name) for path in state_paths]
    sources.append((block_path, GENERATED / "Blocks" / block_path.name))
    previous = {target: target.read_bytes() if target.exists() else None
                for _source, target in sources}
    result = {"compiled": False}
    try:
        for source, target in sources:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source.read_bytes())
        result = gen_segment._build_staged(sources[-1][1], build_dir, seconds, jobs=32)
    except subprocess.TimeoutExpired:
        result = {"compiled": False, "errors": ["block compilation timed out"]}
    finally:
        if not (promote and result.get("compiled")):
            for target, contents in previous.items():
                if contents is None:
                    target.unlink(missing_ok=True)
                else:
                    target.write_bytes(contents)
    result["promoted"] = bool(promote and result.get("compiled"))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cfg", type=Path, default=Path("build/endpoint-cfg/zesu-cfg.json"))
    parser.add_argument("--states", type=Path, required=True)
    parser.add_argument("--leader", action="append", default=[])
    parser.add_argument("--out-dir", type=Path, default=STAGING)
    parser.add_argument("--build-dir", type=Path, default=BUILD_DIR)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--compile", action="store_true")
    parser.add_argument("--promote", action="store_true")
    args = parser.parse_args()
    args.build_dir = args.build_dir.resolve()
    if args.promote and not args.compile:
        parser.error("--promote requires --compile")
    cfg = json.loads(args.cfg.read_text())
    blocks = next(function["blocks"] for function in cfg["functions"]
                  if address(function["start"]) == 0x14d30)
    leaders = {address(value) for value in args.leader}
    if leaders:
        blocks = [block for block in blocks if address(block["start"]) in leaders]
        absent = leaders - {address(block["start"]) for block in blocks}
        if absent:
            parser.error("unknown block leaders: " + ", ".join(hex(value) for value in sorted(absent)))
    states = read_states(args.states)
    for directory in ("States", "Blocks"):
        (args.out_dir / directory).mkdir(parents=True, exist_ok=True)
    # Dune must not discover an open staged proof through include_subdirs.
    (args.out_dir / "dune").write_text("(data_only_dirs States Blocks)\n")
    records = []
    for block in blocks:
        leader = address(block["start"])
        record = {"leader": hex(leader), "hand_lines": 0}
        try:
            source, name = generate(block, states)
            dependencies = list(dict.fromkeys([leader, *map(address, block["successors"])]))
            paths = []
            for value in dependencies:
                path = args.out_dir / "States" / f"State_{value:x}.v"
                path.write_text(state_source(value, states[value]))
                paths.append(path)
            target = args.out_dir / "Blocks" / f"Block_{leader:x}.v"
            target.write_text(source)
            record.update(lemma=name, outcome="staged", generated=str(target))
            if args.compile:
                record.update(compile_module(target, paths, args.build_dir,
                                             args.seconds, args.promote))
                record["outcome"] = "closed" if record["compiled"] else "open"
        except (ValueError, KeyError) as error:
            record.update(outcome="residual", error=str(error))
        records.append(record)
        error = record.get("error", (record.get("errors") or [""])[0])
        print(f"{record['leader']}: {record['outcome']}"
              + (f" {error}" if error else ""), flush=True)
    return 1 if any(record["outcome"] in ("residual", "open") for record in records) else 0


if __name__ == "__main__":
    raise SystemExit(main())
