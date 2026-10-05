#!/usr/bin/env python3
"""Bind proved or pending instruction coverage to native boundary evidence.

A native boundary alone does not supply the universal-inside-iProp table body.
Promotion also requires a compiled adapter with the exact table-body statement.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import generate_table


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def table_statement(pc):
    return (f"⊢ block_table_pre decodeItemBlockTable -∗ "
            f"instr_body {hex(pc)} decodeItemState{pc:x}")


def validate_promotion(block, evidence, adapter, *, design_sha256):
    """Reject partial edges, diagnostic results, debts, and unrelated proofs."""
    pc = generate_table.address(block['entry_pc'])
    successors = sorted(map(generate_table.address, block['successor_pcs']))
    if evidence.get('design_sha256') != design_sha256:
        raise ValueError('The proof binds a different design.')
    if evidence.get('entry_pc') != pc:
        raise ValueError('The proof binds a different block.')
    if sorted(map(generate_table.address, evidence.get('successors', []))) != successors:
        raise ValueError('The proof omits or adds successor edges.')
    if evidence.get('scope') != 'native designed boundary' or not evidence.get('block_closed'):
        raise ValueError('The native boundary is not closed.')
    for proof in (evidence, adapter):
        if not proof.get('compiled') or not proof.get('verified') or proof.get('assumptions') != []:
            raise ValueError('The proof lacks debt-free kernel evidence.')
        groups = proof.get('goal_groups')
        if not isinstance(groups, dict) or any(groups.get(key) != []
                for key in ('goals', 'stack', 'shelf', 'given_up')):
            raise ValueError('The proof has unavailable or nonempty goal groups.')
        if proof.get('inherited_debts') != []:
            raise ValueError('The proof has unavailable or nonempty inherited debts.')
    if adapter.get('statement') != table_statement(pc):
        raise ValueError('The proof has a different table-body signature.')
    if not isinstance(adapter.get('lemma'), str) or not adapter['lemma']:
        raise ValueError('The table adapter has no proof name.')
    return adapter['lemma']


def coverage(cfg, design, native_report, promotions=None, *, design_sha256):
    """Assign every selected instruction to exactly one proved or pending block."""
    structural = generate_table.structure(cfg, design)
    native_blocks = {generate_table.address(row['entry']): row for row in native_report['blocks']}
    designs = {generate_table.address(row['entry_pc']): row for row in design['blocks']}
    if set(native_blocks) != set(designs) or len(native_blocks) != len(native_report['blocks']):
        raise ValueError('The native report omits or repeats a block.')
    slots, instructions = [], []
    promotions = promotions or {}
    for pc, block in sorted(designs.items()):
        native = native_blocks[pc]
        if native.get('entry_provenance', {}).get('design_sha256') != design_sha256:
            raise ValueError('The native report binds a different design.')
        proposal = promotions.get(hex(pc))
        lemma = None
        if proposal:
            if not native.get('block_closed'):
                raise ValueError('The native report does not close the proposed block.')
            lemma = validate_promotion(block, proposal['native'], proposal['adapter'],
                                       design_sha256=design_sha256)
        elif native.get('block_closed'):
            # Native closure still needs a checked table adapter.
            pass
        status = 'proved' if lemma else 'pending'
        slots.append(dict(pc=hex(pc), entry_definition=block.get('entry_definition'),
                          proof_lemma=lemma, status=status,
                          native_outcomes=native.get('outcomes', [])))
        for instruction in range(pc, generate_table.address(block['end_pc_exclusive']), 4):
            instructions.append(dict(pc=hex(instruction), block=hex(pc), status=status))
    if set(promotions) - {hex(pc) for pc in designs}:
        raise ValueError('The promotion names an unknown block.')
    return dict(schema_version=1, label='Structural proof-slot coverage; no composition theorem',
                structural=structural, proof_slots=slots, instructions=instructions,
                proved_instructions=sum(row['status'] == 'proved' for row in instructions),
                pending_instructions=sum(row['status'] == 'pending' for row in instructions))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--recipe', type=Path, default=generate_table.ROOT / 'build/stock-zisk/build-recipe.json')
    parser.add_argument('--cfg', type=Path, required=True)
    parser.add_argument('--design', type=Path, required=True)
    parser.add_argument('--native-report', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = coverage(*(json.loads(path.read_text()) for path in
                        (args.cfg, args.design, args.native_report)), design_sha256=digest(args.design))
    report['manifest_binding'] = generate_table.bound_inputs(args.recipe, args.cfg, args.design)
    report['input_hashes'] = {str(path): digest(path) for path in
                              (args.recipe, args.cfg, args.design, args.native_report, Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
