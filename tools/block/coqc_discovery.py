#!/usr/bin/env python3
"""Retry unavailable native entries without repeating completed primary attempts."""
import argparse
import collections
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import time

import chain_root
import check_entry_bindings
import coqc_primary
import discovery
import entry_schema
import gen_block
import successor_entailment


def load_baseline(path):
    value = json.loads(Path(path).read_text())
    if 'raw_report' in value:
        bound = value['raw_report']
        if coqc_primary.digest(bound['archive_path']) != bound['sha256']:
            raise ValueError('The native baseline archive differs')
        value = json.loads(Path(bound['archive_path']).read_text())
    if len(value['blocks']) != 24 or value.get('contract_closures'):
        raise ValueError('The baseline must contain24 unresolved native entries')
    return value


def checked_reuse(path, rendered):
    evidence = json.loads(Path(path).read_text())
    original = hashlib.sha256(rendered['source'].encode()).hexdigest()
    if (evidence['original_source_sha256'] != original or
            evidence['statement_sha256'] != rendered['statement_sha256'] or
            evidence['primary_timeout'] != 300 or not evidence.get('primary_tactic_entered')):
        raise ValueError('The reused coqc attempt has different native inputs')
    if coqc_primary.digest(evidence['source']) != evidence['source_sha256'] or coqc_primary.digest(evidence['log']) != evidence['log_sha256']:
        raise ValueError('The reused coqc source or capture changed')
    return evidence


def worker(job):
    rendered, out, build, debts = job
    return coqc_primary.run_primary(rendered, out, build, inherited_debts=debts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('baseline', 'full-on', 'historical', 'design', 'cfg', 'binding-report', 'build-dir', 'out', 'measurement-root'):
        parser.add_argument('--'+name, required=True)
    parser.add_argument('--reuse-coqc', action='append', default=[])
    parser.add_argument('--jobs', type=int, default=6)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 6:
        raise ValueError('The driver permits one to six workers')
    root = Path.cwd()
    subprocess.run(['git','merge-base','--is-ancestor',args.measurement_root,'HEAD'],check=True)
    check_entry_bindings.validate_report(args.binding_report,args.design,root)
    baseline=load_baseline(args.baseline)
    selected={b['entry'] for b in baseline['blocks'] if b['outcomes']==['primary-unavailable']}
    if len(selected)!=12:
        raise ValueError('The first fallback pass requires exactly12 unavailable entries')
    design=json.loads(Path(args.design).read_text());cfg=json.loads(Path(args.cfg).read_text())
    historical=json.loads(Path(args.historical).read_text());full=json.loads(Path(args.full_on).read_text())
    states,errors=entry_schema.design_states(design,root,'ZesuSsz.Stock.Closure.index_decodeItem',['  decodeItemSelectedCode -∗'])
    ready,gaps=discovery.prepare(design,cfg,states,gen_block.address(design['entry_pc']),errors)
    if gaps or len(ready)!=24:
        raise ValueError('All24 executable entries must validate')
    reused_candidates={json.loads(Path(p).read_text())['entry_pc']:p for p in args.reuse_coqc}
    out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
    jobs,reused,frozen=[],[],[]
    for row,block,state in ready:
        state['imports']=list(dict.fromkeys(state['imports']+historical['probe_imports']+full['on_additions']))
        rendered=successor_entailment.native_boundary_source(state,block,design,root,
            terminal=discovery.designed_terminal(block,{'workspace':str(root),'terminal':'decodeItemReturnAddress args'}))
        old=next(b for b in baseline['blocks'] if b['entry']==row['entry_pc'])
        bound=old['captures'][0]['native_evidence']
        if coqc_primary.digest(bound['path'])!=bound['sha256']:
            raise ValueError('The frozen native evidence changed')
        previous=json.loads(Path(bound['path']).read_text())
        if hashlib.sha256(rendered['source'].encode()).hexdigest()!=previous['source_sha256']:
            raise ValueError('The native statement or frozen imports changed')
        if row['entry_pc'] not in selected:
            frozen.append({'entry':row['entry_pc'],'outcome':old['outcomes'][0],
                'path':'unchanged completed MCP baseline','measurement_root':baseline['measurement_root'],
                'native_evidence':bound,'first_residual':old['first_residual'],'block_closed':False,'contract_closed':False})
        elif row['entry_pc'] in reused_candidates:
            reused.append(checked_reuse(reused_candidates[row['entry_pc']],rendered))
        else:
            jobs.append((rendered,out/'native'/('block_'+row['entry_pc']),Path(args.build_dir),chain_root.inherited_debts(state)))
    inputs={str(Path(p).resolve()):coqc_primary.digest(p) for p in [args.baseline,args.full_on,args.historical,args.design,args.cfg,args.binding_report,
        __file__,coqc_primary.__file__,coqc_primary.coqc_certificate.__file__,successor_entailment.__file__,chain_root.__file__,entry_schema.__file__,
        'tools/coqc_scratch.sh',str(Path(args.build_dir)/'coqc_recipe.json')]}
    started=time.monotonic();before=discovery.machine()
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        executed=list(pool.map(worker,jobs))
    for path,expected in inputs.items():
        if coqc_primary.digest(path)!=expected:
            raise ValueError('A fallback input changed during execution')
    result={'measurement_root':args.measurement_root,'checkout_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        'label':'Actual designed successor attempts; completed native baselines remain unchanged',
        'inputs':inputs,'workers':args.jobs,'elapsed_seconds':time.monotonic()-started,
        'machine_before':before,'machine_after':discovery.machine(),'new_coqc_attempts':len(executed),
        'reused_coqc_attempts':len(reused),'unchanged_mcp_attempts':len(frozen),
        'coqc_results':reused+executed,'unchanged_baseline':frozen,
        'blocks_closed':sum(bool(r.get('block_closed')) for r in reused+executed),'contract_closures':0,
        'closure_policy':'Exact compiled native Qed, empty assumptions, and no inherited debts certify a block. Missing diagnostic groups do not certify closure.'}
    result['classes']=dict(collections.Counter([r['outcome'] for r in result['coqc_results']]+[r['outcome'] for r in frozen]))
    path=out/'report.json';path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'report':str(path),'sha256':coqc_primary.digest(path),'classes':result['classes'],'blocks_closed':result['blocks_closed']}))


if __name__=='__main__':
    main()
