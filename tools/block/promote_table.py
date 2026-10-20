#!/usr/bin/env python3
"""Bind proved or pending instruction coverage to native boundary evidence.

A native boundary alone does not supply the existential-family table body.
Promotion also requires a compiled adapter with the exact table-body statement.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
import generate_table
from function_names import FunctionNames, prefix_argument


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def table_statement(pc, *, name_prefix="decodeItem"):
    names = FunctionNames(name_prefix)
    return (f"⊢ block_table_pre {names.table} -∗ "
            f"instr_body {hex(pc)} {names.state(pc)}")


def proof_module(proof):
    """Use the checked production module name, never a frozen Boundary name."""
    module, lemma = proof.get('module'), proof.get('lemma')
    identifier = r"[A-Za-z_][A-Za-z0-9_']*"
    if (not isinstance(module, str) or
            not re.fullmatch(identifier + r'(?:\.' + identifier + r')*', module) or
            'Boundary' in module.split('.') or not isinstance(lemma, str) or
            not re.fullmatch(re.escape(module) + r'\.' + identifier, lemma)):
        raise ValueError('The proof lacks a matching production module and lemma name.')
    return module


def validate_promotion(block, evidence, adapter, *, design_sha256, name_prefix="decodeItem"):
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
        proof_module(proof)
    if adapter.get('statement') != table_statement(pc, name_prefix=name_prefix):
        raise ValueError('The proof has a different table-body signature.')
    if not isinstance(adapter.get('lemma'), str) or not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+', adapter['lemma']):
        raise ValueError('The table adapter has no proof name.')
    return adapter['lemma']


def coverage(cfg, design, native_report, promotions=None, *, design_sha256, name_prefix="decodeItem"):
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
                                       design_sha256=design_sha256, name_prefix=name_prefix)
        elif native.get('block_closed'):
            # Native closure still needs a checked table adapter.
            pass
        status = 'proved' if lemma else 'pending'
        slots.append(dict(pc=hex(pc), entry_definition=block.get('entry_definition'),
                          proof_lemma=lemma,
                          proof_module=proposal['adapter']['module'] if lemma else None,
                          status=status,
                          native_outcomes=native.get('outcomes', [])))
        for instruction in range(pc, generate_table.address(block['end_pc_exclusive']), 4):
            instructions.append(dict(pc=hex(instruction), block=hex(pc), status=status))
    if set(promotions) - {hex(pc) for pc in designs}:
        raise ValueError('The promotion names an unknown block.')
    return dict(schema_version=1, label='Structural proof-slot coverage; no composition theorem',
                structural=structural, proof_slots=slots, instructions=instructions,
                proved_instructions=sum(row['status'] == 'proved' for row in instructions),
                pending_instructions=sum(row['status'] == 'pending' for row in instructions))




def load_promotions(path):
    """Load hash-bound native and adapter certificates from trusted MCP output."""
    manifest = json.loads(path.read_text())
    proposals = {}
    hashes = {str(path): digest(path)}
    for pc, binding in manifest.items():
        proposal = {}
        for kind in ('native', 'adapter'):
            record = binding[kind]
            evidence_path = (path.parent / record['path']).resolve()
            if digest(evidence_path) != record['sha256']:
                raise ValueError('The promotion evidence hash differs.')
            evidence = json.loads(evidence_path.read_text())
            source = evidence.get('source_binding')
            if not isinstance(source, dict):
                raise ValueError('The promotion lacks a proof-source binding.')
            source_path = (evidence_path.parent / source['path']).resolve()
            if digest(source_path) != source['sha256']:
                raise ValueError('The promotion proof-source hash differs.')
            hashes[str(evidence_path)] = record['sha256']
            hashes[str(source_path)] = source['sha256']
            proposal[kind] = evidence
        proposals[pc] = proposal
    return proposals, hashes

def render_slots(report, *, name_prefix="decodeItem"):
    """Generate typed references only. Pending slots introduce no proposition."""
    names = FunctionNames(name_prefix)
    slots = [slot for slot in report['proof_slots'] if slot['status'] == 'proved']
    modules = sorted({proof_module({'module': slot['proof_module'],
                                   'lemma': slot['proof_lemma']}) for slot in slots})
    lines = ['Require Import ZesuSsz.Automation.All.',
             'Require Import ZesuSsz.Automation.Approved.',
             f'Require Import {names.hints}.',
             'Require Import isla.riscv64.riscv64.',
             'Require Import ZesuSsz.Automation.BlockTable.',
             f'Require Import {names.table_module}.']
    lines.extend(f'Require Import {module}.' for module in modules)
    lines += ['', '(* Pending slots have no proof term. No composition theorem is generated. *)',
              'Section promoted_block_bodies.', 'Context `{!islaG Sigma} `{!threadG}.', '']
    for slot in slots:
        pc = generate_table.address(slot['pc'])
        lines += [f'Definition {names.prefix}PromotedBody{pc:x} :',
                  f'  {table_statement(pc, name_prefix=name_prefix)} :=', f"  {slot['proof_lemma']}.", '']
    lines += ['End promoted_block_bodies.', '']
    lines.extend(f"Print Assumptions {names.prefix}PromotedBody{generate_table.address(slot['pc']):x}."
                 for slot in slots)
    return '\n'.join(lines) + '\n'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--function', type=prefix_argument, default='decodeItem')
    parser.add_argument('--recipe', type=Path, default=generate_table.ROOT / 'build/stock-zisk/build-recipe.json')
    parser.add_argument('--cfg', type=Path)
    parser.add_argument('--design', type=Path)
    parser.add_argument('--native-report', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rocq-output', type=Path)
    parser.add_argument('--promotions', type=Path, help='Hash-bound kernel certificates; diagnostic captures are not certificates.')
    parser.add_argument('--complete-native', type=lambda value: int(value, 0),
                        help='Generate all consumers of this named production closure.')
    parser.add_argument('--workspace', type=Path, default=generate_table.ROOT)
    parser.add_argument('--production-module')
    parser.add_argument('--production-lemma')
    parser.add_argument('--native-status-table', type=Path)
    parser.add_argument('--no-historical-evidence', action='store_true',
                        help='Skip unavailable historical measurements, with an explicit reason.')
    parser.add_argument('--reason', help='Record why historical evidence is unavailable.')
    parser.add_argument('--dry-run', action='store_true', help='Emit complete-promotion sources without verification or a success claim.')
    parser.add_argument('--verification-directory', type=Path)
    parser.add_argument('--mcp-python', help='Pinned Python interpreter with the rocq-mcp package.')
    args = parser.parse_args()
    if args.no_historical_evidence and (args.complete_native is None or not args.reason or not args.reason.strip()):
        parser.error('--no-historical-evidence requires --complete-native and a nonempty --reason.')
    if args.reason is not None and not args.no_historical_evidence:
        parser.error('--reason requires --no-historical-evidence.')
    if args.complete_native is not None:
        if not all((args.production_module, args.production_lemma)):
            parser.error('Complete promotion requires the named production module and lemma.')
        if args.function == 'decodeItem' and args.native_status_table is None and not args.no_historical_evidence:
            parser.error('Complete decodeItem promotion requires its retained status table.')
        from complete_promotion import complete
        complete(args.workspace, args.complete_native, args.production_module,
                 args.production_lemma, args.output, args.native_status_table,
                 dry_run=args.dry_run, verification_directory=args.verification_directory,
                 mcp_python=args.mcp_python, name_prefix=args.function,
                 no_historical_evidence=args.no_historical_evidence, reason=args.reason)
        return
    if not all((args.cfg, args.design, args.native_report)):
        parser.error('Coverage generation requires --cfg, --design, and --native-report.')
    promotions, promotion_hashes = load_promotions(args.promotions) if args.promotions else ({}, {})
    report = coverage(*(json.loads(path.read_text()) for path in
                        (args.cfg, args.design, args.native_report)), promotions=promotions, design_sha256=digest(args.design), name_prefix=args.function)
    report['manifest_binding'] = generate_table.bound_inputs(args.recipe, args.cfg, args.design)
    report['input_hashes'] = {str(path): digest(path) for path in
                              (args.recipe, args.cfg, args.design, args.native_report, Path(__file__))}
    report['input_hashes'].update(promotion_hashes)
    if args.rocq_output:
        args.rocq_output.parent.mkdir(parents=True, exist_ok=True)
        args.rocq_output.write_text(render_slots(report, name_prefix=args.function))
        report['generated_hashes'] = {str(args.rocq_output): digest(args.rocq_output)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
