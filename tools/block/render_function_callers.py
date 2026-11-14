"""Render the block callers of one function from its rendered FP301 entries.

A block gets a caller when its own entry and the entry of every CFG successor
rendered. Its exit premises are the successors' `instr_pre` entries in address
order. A return block's premise is the function-return package at
returnAddress. A block that ends in a call (a profile `calls` row) also gets the
callee spec at the callee address, `instr_pre CALLEE SPEC`; its successor is
the return site. A block without successors needs the function-return package; this
renderer refuses it until that package exists. A block that tail-jumps to a callee
with a profile `tail_calls` row gets the callee spec and the function-return package:
the callee returns to returnAddress. Each caller's proof is exactly
`zesu_block2.`; no other proof text is written.

Usage: render_function_callers.py --function NAME --entries RESULT.json
       --cfg FUNCTION.json --output DIR
"""
from pathlib import Path
import argparse, hashlib, json, re, sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from function_profiles import load_profile, return_sites
from render_fp301_statements import (render_block_caller, return_precondition, slot_suffix,
                                     successor_precondition)


def bind(path):
    path = Path(path)
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def return_site(sites, start, end):
    """The suffix of the return site inside [start, end); None if none lies there."""
    if len(sites) <= 1:
        return sites[0][0] if sites else ''   # One package serves every return block.
    inside = [suffix for suffix, design in sites
              if end is not None and start <= int(design['return_instruction_pc'], 0) < end]
    return inside[0] if len(inside) == 1 else None


def plan_callers(profile, cases, function):
    """Return (block, slot, successors, refusal) for each profile block, one row per entry slot.

    A block with entry slots (a duplicated join and the non-cut blocks after it) gets
    one caller per slot. Each successor is (name, slot): a successor with slots
    contributes the slots whose incoming edge leaves this block (and this block's slot);
    a successor slot that no path reaches is no premise.
    """
    rendered = {case['pc'] for case in cases
                if case['status'] == 'source_declarations_rendered' and 'slot' not in case}
    slot_cases = {}
    for case in cases:
        if 'slot' in case:
            slot_cases.setdefault(case['pc'], []).append(case)
    blocks = {block['start']: sorted(block['successors']) for block in function['blocks']}
    ends = {block['start']: block.get('end') for block in function['blocks']}
    sites = return_sites(profile)
    rows = []
    for suffix in profile['blocks']:
        pc = int(profile.pc(suffix), 16)
        own = slot_cases.get(hex(pc))
        for slot in [case['slot']['index'] for case in own] if own else [None]:
            rows.append(_plan_caller(profile, suffix, pc, slot, own, rendered, slot_cases, blocks, ends, sites))
    return rows


def _block_key(profile, target):
    """The design-table key of a successor address; None outside the function's blocks."""
    try:
        key = profile.key(target)
    except ValueError:
        return None
    return key if key in profile['blocks'] else None


def _plan_caller(profile, suffix, pc, slot, own, rendered, slot_cases, blocks, ends, sites):
    successors = blocks[pc]
    names = [_block_key(profile, target) for target in successors]
    outside = [target for name, target in zip(names, successors) if name is None]
    if outside:
        tails = {int(call['callee_pc'], 16) for call in profile.get('tail_calls', [])
                 if pc <= int(call['call_site_pc'], 16) < ends[pc]}
        if len(outside) != len(successors) or set(outside) - tails:
            return (suffix, slot, [(name or hex(target), None) for name, target in zip(names, successors)],
                    'successor outside the function (tail jump without a tail_calls row)')
        # A tail jump to a callee with a profile spec: the callee returns to returnAddress,
        # so the block exits as a return block does, through the callee spec.
        successors, names = [], []
    exits, missing = [], []
    for name, target in zip(names, successors):
        if hex(target) not in slot_cases:
            exits.append((name, None))
            if profile.pc(name) not in rendered:
                missing.append(name)
            continue
        for case in slot_cases[hex(target)]:
            if case['slot']['predecessor_pc'] == hex(pc) and case['slot']['predecessor_slot'] == slot:
                exits.append((name, case['slot']['index']))
                if case['status'] != 'source_declarations_rendered':
                    missing.append(name + slot_suffix(case['slot']['index']))
    if (hex(pc) not in rendered if slot is None else
            next(case for case in own if case['slot']['index'] == slot)['status'] != 'source_declarations_rendered'):
        refusal = 'own entry not rendered'
    elif not successors:
        site = return_site(sites, pc, ends[pc])
        package = 'function_return' + ('_' + site if site else '')
        refusal = None if site is not None and package in rendered else 'function-return package not rendered'
    else:
        refusal = ('successor entry not rendered: ' + ', '.join(missing)) if missing else None
    return (suffix, slot, exits, refusal)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--function', required=True)
    parser.add_argument('--entries', type=Path, required=True)
    parser.add_argument('--cfg', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    options = parser.parse_args()
    profile = load_profile(options.function)
    result = json.loads(options.entries.read_text())
    function = json.loads(options.cfg.read_text())['functions'][0]
    output = options.output
    output.mkdir(parents=True, exist_ok=False)
    table = []
    for suffix, slot, successors, refusal in plan_callers(profile, result['cases'], function):
        row = {'case': suffix + slot_suffix(slot), 'pc': profile.pc(suffix),
               'successors': [name + slot_suffix(index) for name, index in successors],
               # A slot row names its block (entry module Pilot<block>Entries) and slot index.
               **({'block': suffix, 'slot': slot} if slot is not None else {})}
        if refusal:
            table.append({**row, 'status': 'refused', 'reason': refusal})
            continue
        modules = [suffix, *dict.fromkeys(name for name, _ in successors)]
        imports = [profile.qualified('Pilot' + name + kind) for name in modules
                   for kind in ('Entries', 'Structural')]
        preconditions = [successor_precondition(profile, name, index) for name, index in successors]
        if not successors:
            # A return block exits to the function-return package at returnAddress.
            start = int(row['pc'], 16)
            end = next(block.get('end') for block in function['blocks'] if block['start'] == start)
            site = return_site(return_sites(profile), start, end)
            imports += [profile.qualified('FunctionReturn' + site + kind) for kind in ('Entries', 'Structural')]
            preconditions.append(return_precondition(profile, site))
        block = next(row for row in function['blocks'] if row['start'] == int(profile.pc(suffix), 16))
        for call in profile.get('calls', []) + profile.get('tail_calls', []):
            if block['start'] <= int(call['call_site_pc'], 16) < block['end']:
                imports.append(call['spec_module'])
                preconditions.append('instr_pre ' + call['callee_pc'] + ' ('
                                     + call['spec_module'] + '.' + call['spec'] + ')%I')
        source = render_block_caller(profile, suffix, preconditions, imports, slot)
        if source.count('Proof.\n  zesu_block2.\nQed.\n') != 1 or re.search(r'\b(?:Ltac|Admitted|Axiom)\b|::=', source):
            raise ValueError('A caller has more than its block proof: ' + suffix)
        path = output / ('Caller' + suffix + slot_suffix(slot) + '.v')
        path.write_text(source)
        table.append({**row, 'status': 'rendered', 'caller': bind(path),
                      'lemma': 'DesignedBoundary_' + profile.pc(suffix)[2:] + slot_suffix(slot),
                      'preconditions': preconditions})
    summary = {'status': 'SOURCE_DECLARATIONS_ONLY', 'function': profile.name, 'entries': bind(options.entries),
               'cfg': bind(options.cfg), 'rows': table,
               'rendered': sum(row['status'] == 'rendered' for row in table),
               'refused': sum(row['status'] == 'refused' for row in table), 'proof_ran': False}
    (output / 'CALLERS.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'rendered': summary['rendered'], 'refused': summary['refused']}))


if __name__ == '__main__':
    main()
