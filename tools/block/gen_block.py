#!/usr/bin/env python3
"""Generate whole-block proofs from inferred states and the pinned CFG.

States are JSON records with entry, binders, coq, spatial, and imports.
The context field can replace coq and spatial in a reached probe record.
The arguments field names a state's application in its predecessor.
No missing resource or successor state is guessed.
The standard_call_frame option explicitly strengthens recorded states
with the system and temporary ownership required by WP2(d).

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
            states[leader] = row
    return states


def state_source(leader: int, state: dict) -> str:
    if state.get("outcome", "reached") != "reached":
        raise ValueError(f"state {hex(leader)} did not reach its boundary")
    if "context" in state:
        coq, persistent, spatial = gen_boundary.sections(state["context"])
        # Code and callee premises belong to the block statement. MMIO
        # ownership belongs to the state even when Iris keeps it persistent.
        spatial += [atom for atom in persistent if atom.startswith('mmio_range ')]
        coq = [(name, kind) for name, kind in coq if not name.startswith('BLK_STOP_')]
    else:
        coq, spatial = state.get("coq", []), state["spatial"]
    parameters = set(gen_boundary.explicit_arguments(state['binders']).split())
    named = {name for name, _kind in coq}
    coq += [(name, kind) for name, kind in state.get('parameter_types', {}).items()
            if name in parameters and name not in named]
    values = {}
    for row in state.get('resource_values', []):
        source = gen_boundary.spatial_atoms(row['source'])[0]
        value, kind = row['value'], row['type'].removeprefix('(').removesuffix(')')
        if '↦ᵣ' in source:
            width = re.fullmatch(r'bv (\d+)', kind)
            if not width:
                raise ValueError(f"unsupported register value type: {kind}")
            values[source] = (source.split('↦ᵣ')[0] +
                              f'↦ᵣ RVal_Bits (@bv_to_bvn {width[1]} ({value}))')
        elif '↦ₘ' in source:
            values[source] = source.split('↦ₘ')[0] + f'↦ₘ ({value} : {kind})'
        elif source.startswith('instr_pre '):
            width = re.fullmatch(r'bv (\d+)', kind)
            if not width:
                raise ValueError(f"unsupported instruction address type: {kind}")
            values[source] = source.replace('bv_unsigned', '@bv_unsigned ' + width[1], 1)
    spatial = [values.get(' '.join(atom.split()), atom) for atom in spatial]
    collections = {'reg_col ' + row['source']: 'reg_col ' + row['value']
                   for row in state.get('register_collections', [])}
    # InstrSpecs.Machine declares both spellings as zesu_sys_regs.
    spatial = [collections.get(' '.join(atom.split()), atom).replace(
        'reg_col zesu_instr_sys_regs', 'reg_col zesu_ram_sys_regs') for atom in spatial]
    spatial = gen_boundary.normalize_temporaries(
        [atom for resource in spatial for atom in gen_boundary.spatial_atoms(resource)])
    if state.get("standard_call_frame", False):
        spatial = with_standard_call_frame(spatial)
    source = gen_boundary.boundary_source(
        f"State_{leader:x}", state["binders"], coq, spatial,
        seal=len(spatial) > gen_boundary.RULE_20_CONJUNCTS,
        call_resources=True, sorts=state.get("local_sorts", state.get("sorts")))
    imports = ["ZesuSsz.Automation.All", "ZesuSsz.Automation.SealedCoverage",
               "isla.riscv64.riscv64", *state.get("imports", [])]
    return ("(* Generated by tools/block/gen_block.py. Do not edit. *)\n"
            + "\n".join(f"Require Import {module}." for module in dict.fromkeys(imports))
            + "\n\n" + source)


def with_standard_call_frame(atoms: list[str]) -> list[str]:
    """Add the approved call frame while preserving recorded resources."""
    atoms = list(atoms)
    if 'reg_col zesu_ram_sys_regs' not in atoms:
        atoms.insert(0, 'reg_col zesu_ram_sys_regs')
    if any(atom.startswith('reg_col ') and 'tmp_registers' in atom for atom in atoms):
        return atoms
    for atom in atoms:
        if atom.startswith('reg_col ') and any(
                f'KindReg "{register}"' in atom for register in gen_boundary.TMP_REGISTERS):
            raise ValueError('a temporary register remains in an unsupported collection')
    # Complete a partial collection with the missing registers. Recorded
    # exact values and predicates must stay in the resulting collection.
    owned = {match.group(1) for atom in atoms
             if (match := re.match(r'"(x\d+)"\s*↦ᵣ', atom))}
    for register in gen_boundary.TMP_REGISTERS:
        if register not in owned:
            atoms.append(f'"{register}" ↦ᵣ: fun r => '
                         '⌜valu_has_shape r (BitsShape 64)⌝ ∗ True')
    return gen_boundary.normalize_temporaries(atoms)


def state_application(leader: int, state: dict) -> str:
    args = state.get("arguments", gen_boundary.explicit_arguments(state["binders"]))
    return f"State_{leader:x} {args}".strip()


def generate(block: dict, states: dict[int, dict]) -> tuple[str, str]:
    """Reuse segment generation with guarded successor premises."""
    leader, end = address(block["start"]), address(block["end"])
    successors = [address(value) for value in block["successors"]]
    needed = list(dict.fromkeys([leader, *successors]))
    missing = [hex(value) for value in needed if value not in states]
    if missing:
        raise ValueError("missing inferred states: " + ", ".join(missing))
    for value in needed:
        state_source(value, states[value])
    _premises, _modules, _unknown = call_sites.premises(leader, end, strict=True)
    spec = {"name": f"block_{leader:x}", "entry": hex(leader), "exit": hex(end),
            "binders": states[leader]["binders"],
            "imports": [f"{STATE_MODULE}.State_{value:x}" for value in needed],
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
