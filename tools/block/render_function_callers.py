"""Render the block callers of one function from its rendered FP301 entries.

A block gets a caller when its own entry and the entry of every CFG successor
rendered. Its exit premises are the successors' `instr_pre` entries in address
order. A block that ends in a call (a profile `calls` row) also gets the
callee spec at the callee address, `instr_pre CALLEE SPEC`; its successor is
the return site. A block without successors needs the function-return package; this
renderer refuses it until that package exists. Each caller's proof is exactly
`zesu_block2.`; no other proof text is written.

Usage: render_function_callers.py --function NAME --entries RESULT.json
       --cfg FUNCTION.json --output DIR
"""
from pathlib import Path
import argparse, hashlib, json, re, sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from function_profiles import load_profile
from render_fp301_statements import render_block_caller, successor_precondition


def bind(path):
    path = Path(path)
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def plan_callers(profile, cases, function):
    """Return (block, successors, refusal) for each profile block."""
    rendered = {case['pc'] for case in cases if case['status'] == 'source_declarations_rendered'}
    blocks = {block['start']: sorted(block['successors']) for block in function['blocks']}
    rows = []
    for suffix in profile['blocks']:
        pc = int(profile.pc(suffix), 16)
        successors = blocks[pc]
        names = [format(target, 'x')[-len(suffix):] for target in successors]
        if any(profile.pc(name) != hex(target) for name, target in zip(names, successors)):
            raise ValueError('A successor lies outside the profile address prefix: ' + suffix)
        if hex(pc) not in rendered:
            refusal = 'own entry not rendered'
        elif not successors:
            refusal = 'function-return package not rendered'
        else:
            missing = [name for name in names if profile.pc(name) not in rendered]
            refusal = ('successor entry not rendered: ' + ', '.join(missing)) if missing else None
        rows.append((suffix, names, refusal))
    return rows


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
    for suffix, successors, refusal in plan_callers(profile, result['cases'], function):
        row = {'case': suffix, 'pc': profile.pc(suffix), 'successors': successors}
        if refusal:
            table.append({**row, 'status': 'refused', 'reason': refusal})
            continue
        imports = [profile.qualified('Pilot' + name + kind) for name in [suffix, *successors]
                   for kind in ('Entries', 'Structural')]
        preconditions = [successor_precondition(profile, name) for name in successors]
        block = next(row for row in function['blocks'] if row['start'] == int(profile.pc(suffix), 16))
        for call in profile.get('calls', []):
            if block['start'] <= int(call['call_site_pc'], 16) < block['end']:
                imports.append(call['spec_module'])
                preconditions.append('instr_pre ' + call['callee_pc'] + ' ('
                                     + call['spec_module'] + '.' + call['spec'] + ')%I')
        source = render_block_caller(profile, suffix, preconditions, imports)
        if source.count('Proof.\n  zesu_block2.\nQed.\n') != 1 or re.search(r'\b(?:Ltac|Admitted|Axiom)\b|::=', source):
            raise ValueError('A caller has more than its block proof: ' + suffix)
        path = output / ('Caller' + suffix + '.v')
        path.write_text(source)
        table.append({**row, 'status': 'rendered', 'caller': bind(path),
                      'lemma': 'DesignedBoundary_' + profile.pc(suffix)[2:],
                      'preconditions': preconditions})
    summary = {'status': 'SOURCE_DECLARATIONS_ONLY', 'function': profile.name, 'entries': bind(options.entries),
               'cfg': bind(options.cfg), 'rows': table,
               'rendered': sum(row['status'] == 'rendered' for row in table),
               'refused': sum(row['status'] == 'refused' for row in table), 'proof_ran': False}
    (output / 'CALLERS.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'rendered': summary['rendered'], 'refused': summary['refused']}))


if __name__ == '__main__':
    main()
