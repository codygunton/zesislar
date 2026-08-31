#!/usr/bin/env python3
"""Generate one fast Rocq lookup for a set of split Islaris traces."""

import argparse
import re
from pathlib import Path


INSTRUCTION = re.compile(r"^\s*([0-9a-f]+):\s+[0-9a-f]+\s+(.+)$")
SPEC = re.compile(r"^//@spec:\s+(.+)$")


def lookup_tree(entries: list[tuple[int, str]], indent: str = "  ") -> list[str]:
    if not entries:
        return [f"{indent}None"]
    middle = len(entries) // 2
    address, trace = entries[middle]
    lines = [f"{indent}match Z.compare address 0x{address:x} with",
             f"{indent}| Datatypes.Eq => Some ({trace})",
             f"{indent}| Datatypes.Lt =>"]
    lines.extend(lookup_tree(entries[:middle], indent + "  "))
    lines.append(f"{indent}| Datatypes.Gt =>")
    lines.extend(lookup_tree(entries[middle + 1:], indent + "  "))
    lines.append(f"{indent}end")
    return lines


def instr_resource_proof(entries: list[tuple[int, str]], indent: str = "  ") -> list[str]:
    if not entries:
        return [f"{indent}done."]
    address, _ = entries[0]
    lines = [
        f"{indent}iSplitL.",
        f"{indent}- iPoseProof (\"Hcode\" $! 0x{address:x} with \"[]\") as \"Hinstr\".",
        f"{indent}  {{ iPureIntro. rewrite lookup_a{address:x}. eauto. }}",
        f"{indent}  iEval (rewrite lookup_a{address:x}) in \"Hinstr\". iExact \"Hinstr\".",
        f"{indent}- {{",
    ]
    lines.extend(instr_resource_proof(entries[1:], indent + "  "))
    lines.append(f"{indent}  }}")
    return lines


def generate(
    dump_dir: Path,
    output_dir: Path,
    first_block: int,
    theory_prefix: str = "write_success",
    hint_groups: dict[str, tuple[int, int]] | None = None,
) -> None:
    blocks: list[tuple[int, Path]] = []
    for dump in dump_dir.glob("block_*.dump"):
        number = int(dump.stem.removeprefix("block_"))
        if number >= first_block:
            blocks.append((number, dump))
    blocks.sort()

    entries_by_address: dict[int, str] = {}
    specs_by_address: dict[int, tuple[str, str, int]] = {}
    for number, dump in blocks:
        suffix = f"{number:02d}"
        pending_spec = None
        for line in dump.read_text().splitlines():
            spec_match = SPEC.match(line)
            if spec_match:
                pending_spec = spec_match.group(1)
                continue
            match = INSTRUCTION.match(line)
            if match:
                address = int(match.group(1), 16)
                module = f"IslaTraces.{theory_prefix}_{suffix}.a{address:x}"
                entries_by_address[address] = f"{module}.a{address:x}"
                if pending_spec is not None:
                    term = re.sub(r"\bpc\b", f"0x{address:x}", pending_spec)
                    specs_by_address[address] = (
                        term,
                        f"Require Import IslaTraces.{theory_prefix}_{suffix}.a{address:x}_spec.",
                        number,
                    )
                pending_spec = None
    entries = sorted(entries_by_address.items())
    spec_entries = sorted(
        (address, term) for address, (term, _, _) in specs_by_address.items()
    )
    spec_imports = [
        import_line for _, import_line, _ in specs_by_address.values()
    ]

    output_dir.mkdir(parents=True, exist_ok=True)
    theories = "\n".join(
        f"  IslaTraces.{theory_prefix}_{number:02d}" for number, _ in blocks)
    (output_dir / "dune").write_text(
        "(include_subdirs qualified)\n"
        "(coq.theory\n"
        f" (name IslaTraces.{theory_prefix}_blocks)\n"
        f" (theories\n{theories}\n ))\n")

    imports = "\n".join(
        f"From IslaTraces.{theory_prefix}_{number:02d} Require Import instrs."
        for number, _ in blocks)
    source = [
        "From Coq Require Import ZArith.ZArith.",
        "Require Import isla.isla.",
        "Require Import InstrSpecs.Lookup.",
        "Require Import InstrSpecs.Specs.",
        "Import ListNotations.",
        imports,
        *spec_imports,
        "Definition lookup (address : Z) : option isla_trace :=",
        *lookup_tree(entries),
        ".",
    ]
    trace_by_address = dict(entries)
    for address, _ in entries:
        source.extend([
            f"Lemma lookup_a{address:x} :",
            f"  lookup 0x{address:x} = Some ({trace_by_address[address]}).",
            "Proof.",
            "  unfold lookup.",
            f"  change (Some ({trace_by_address[address]}) = Some ({trace_by_address[address]})).",
            "  reflexivity.",
            "Qed.",
        ])
    source.extend([
        "Definition body_lookup `{!islaG Sigma} `{!threadG}",
        "    (address : Z) : option (iProp Sigma) :=",
        *lookup_tree(spec_entries),
        ".",
    ])
    for address, term in spec_entries:
        source.extend([
            f"Lemma body_lookup_a{address:x} `{{!islaG Sigma}} `{{!threadG}} :",
            f"  body_lookup 0x{address:x} = Some ({term}).",
            "Proof.",
            "  unfold body_lookup.",
            f"  change (Some ({term}) = Some ({term})).",
            "  reflexivity.",
            "Qed.",
            f"Definition find_body_a{address:x}_inst",
            "    `{!islaG Sigma} `{!threadG} :=",
            "  [instance find_in_context_instr_body_lookup_resources_at",
            f"    0x{address:x} body_lookup ({term})",
            f"    body_lookup_a{address:x} with FICSyntactic].",
            f"#[export] Hint Extern 8",
            f"  (FindInContext (FindInstrKind {address} ?later) FICSyntactic) =>",
            f"  exact find_body_a{address:x}_inst : typeclass_instances.",
        ])
    source.extend([
        "Definition spec_instr_resources `{!islaG Sigma} `{!threadG} : iProp Sigma :=",
        "  instr_body_lookup_resources body_lookup.",
        "Global Instance : LithiumUnfold (@spec_instr_resources) := I.",
    ])
    (output_dir / "Index.v").write_text("\n".join(source) + "\n")

    for number, _ in blocks:
        addresses = sorted(
            address for address, (_, _, block) in specs_by_address.items()
            if block == number
        )
        hints = [
            f"From IslaTraces.{theory_prefix}_blocks Require Import Index.",
            *(f"#[export] Existing Instance find_body_a{address:x}_inst | 8."
              for address in addresses),
        ]
        (output_dir / f"Hints{number}.v").write_text("\n".join(hints) + "\n")

    for name, (start, stop) in (hint_groups or {}).items():
        addresses = sorted(
            address for address in specs_by_address if start <= address < stop
        )
        hints = [
            f"From IslaTraces.{theory_prefix}_blocks Require Import Index.",
            *(f"#[export] Existing Instance find_body_a{address:x}_inst | 8."
              for address in addresses),
        ]
        (output_dir / f"Hints{name}.v").write_text("\n".join(hints) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dump-dir", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--first-block", type=int, default=0)
    parser.add_argument("--theory-prefix", default="write_success")
    parser.add_argument("--hint-group", action="append", default=[])
    args = parser.parse_args()
    hint_groups = {}
    for item in args.hint_group:
        name, start, stop = item.split(":")
        hint_groups[name] = (int(start, 0), int(stop, 0))
    generate(
        args.dump_dir,
        args.output_dir,
        args.first_block,
        args.theory_prefix,
        hint_groups,
    )


if __name__ == "__main__":
    main()
