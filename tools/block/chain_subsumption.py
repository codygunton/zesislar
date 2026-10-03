"""Compile conservative loop handoffs without guessing substitutions."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'det'))
import gen_boundary

ROOT = Path(__file__).resolve().parents[2]


def subsumption_source(post_state: dict, header_state: dict) -> str:
    """Use identical actual parameter lists; retain every captured resource."""
    binders = post_state['binders']
    if header_state['binders'] != binders:
        raise ValueError('explicit binder substitution required')
    for key in ('root_sha', 'binary_sha256', 'root_entry'):
        if post_state.get(key) != header_state.get(key):
            raise ValueError(f'incompatible root provenance: {key}')
    arguments = gen_boundary.explicit_arguments(binders)
    declarations = []
    imports = ['ZesuSsz.Automation.All', 'isla.riscv64.riscv64']
    for name, state in [('ChainPost', post_state), ('ChainHeader', header_state)]:
        if state.get('outcome', 'reached') != 'reached':
            raise ValueError('state did not reach its boundary')
        if state.get('witnesses') or state.get('arguments', arguments) != arguments:
            raise ValueError('explicit parameter substitution required')
        if 'context' in state:
            coq, persistent, spatial = gen_boundary.sections(state['context'])
            if persistent:
                raise ValueError('persistent context requires an explicit declaration')
        else:
            coq, spatial = state.get('coq', []), state['spatial']
        imports.extend(state.get('imports', []))
        declarations.append(gen_boundary.boundary_source(
            name, binders, coq, spatial, seal=False, call_resources=False,
            sorts=state.get('local_sorts', state.get('sorts'))))
    return ('\n'.join(f'Require Import {module}.' for module in dict.fromkeys(imports))
            + '\n\n' + '\n'.join(declarations)
            + f'\nLemma chain_subsumption {binders} :\n'
            + f'  ChainPost {arguments} -∗ ChainHeader {arguments}.\n'
            + 'Proof.\n  unfold ChainPost, ChainHeader.\n  zesu_block.\n'
            + '  all: match goal with |- ?G => idtac "SUBSUMPTION-RESIDUAL" G end.\n'
            + 'Show.\nQed.\nPrint Assumptions chain_subsumption.\n')


def check_subsumption(post_state: dict, header_state: dict,
                      build_dir: str | Path, seconds: int) -> dict:
    """Return closed only after the compiler accepts Qed without assumptions."""
    record = {'outcome': 'rejected', 'closed': False}
    if not 0 < seconds <= 300:
        return dict(record, reason='proof limit must be between 1 and 300 seconds')
    try:
        source = subsumption_source(post_state, header_state)
    except (ValueError, KeyError, TypeError) as error:
        return dict(record, reason=str(error))
    directory = Path(build_dir).resolve()
    digest = hashlib.sha256(source.encode()).hexdigest()[:16]
    target = directory / 'chain_subsumption' / f'Subsumption_{digest}.v'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(source)
    log = target.with_suffix('.log')
    with log.open('w') as output:
        result = subprocess.run(
            ['timeout', '--kill-after=5s', str(seconds),
             str(ROOT / 'tools/coqc_scratch.sh'), str(target), str(directory)],
            cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=False)
    text = log.read_text()
    closed = result.returncode == 0 and 'Closed under the global context' in text
    record.update(outcome='closed' if closed else 'residual', closed=closed,
                  rc=result.returncode, source=str(target), log=str(log),
                  residual=text, source_sha256=hashlib.sha256(source.encode()).hexdigest())
    target.with_suffix('.json').write_text(json.dumps(record, indent=2))
    return record
