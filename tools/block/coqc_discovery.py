#!/usr/bin/env python3
"""Retry unavailable native entries without repeating completed primary attempts."""
import argparse
import collections
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

import chain_root
import check_entry_bindings
import coqc_primary
import discovery
import entry_schema
import gen_block
import production_modules
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
    rendered, out, build, debts, *policy = job
    return coqc_primary.run_primary(rendered, out, build, inherited_debts=debts,
                                    cpu_seconds=policy[0] if policy else None,
                                    memory_gib=policy[1] if len(policy)>1 else 6)


def module_limits(values):
    result = {}
    for value in values:
        pc, cpu, memory = value.split(':')
        if pc in result:
            raise ValueError('A completion entry has duplicate limits')
        result[pc] = coqc_primary.budget_policy(cpu_seconds=int(cpu), memory_gib=int(memory), entry_pc=pc)
    return result


def selection(baseline, fresh):
    if fresh:
        return {b['entry'] for b in baseline['blocks']}
    result = {b['entry'] for b in baseline['blocks'] if b['outcomes'] == ['primary-unavailable']}
    if len(result) != 12:
        raise ValueError('The first fallback pass requires exactly12 unavailable entries')
    return result


def native_import_targets(sources, root):
    """Extract physical targets without truncating qualified Rocq names."""
    targets=set()
    for source in sources:
        for group in re.findall(r'^Require Import ([^\n]+)\.$',source,re.M):
            for name in group.split():
                if name.startswith('ZesuSsz.'):
                    target=Path(name.replace('.','/')+'.vo')
                    if (Path(root)/target.with_suffix('.v')).is_file():
                        targets.add(str(target))
    if not targets:
        raise ValueError('The native import parser selected zero targets')
    return sorted(targets)


def emit_native_production(records, sources, root):
    """Emit current prepared sources only for certified native closures."""
    return [production_modules.emit(sources[record['entry_pc']], 'native', root)
            for record in records if record.get('block_closed')]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('baseline', 'full-on', 'historical', 'design', 'cfg', 'binding-report', 'build-dir', 'out', 'measurement-root'):
        parser.add_argument('--'+name, required=True)
    parser.add_argument('--reuse-coqc', action='append', default=[])
    parser.add_argument('--jobs', type=int, default=6)
    parser.add_argument('--all', action='store_true', help='Run all entries with current automation; do not reuse old attempts')
    parser.add_argument('--additional-import', action='append', default=[])
    parser.add_argument('--profiles', type=Path)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--emit-production', action='store_true',
                        help='Emit named production modules for closed current native sources; compile them through Dune before promotion')
    parser.add_argument('--cpu-seconds', type=int, help='Explicit CPU completion mode; no wall cutoff')
    parser.add_argument('--module-limit', action='append', default=[], metavar='PC:CPU:GiB')
    args = parser.parse_args()
    default_policy = coqc_primary.budget_policy(cpu_seconds=args.cpu_seconds)
    overrides = module_limits(args.module_limit)
    def policy_for(pc):
        return overrides.get(pc, default_policy)
    if not 1 <= args.jobs <= 6:
        raise ValueError('The driver permits one to six workers')
    root = Path.cwd()
    subprocess.run(['git','merge-base','--is-ancestor',args.measurement_root,'HEAD'],check=True)
    if args.all and args.reuse_coqc:
        raise ValueError('A changed-automation all-entry run cannot reuse old attempts')
    if subprocess.check_output(['git','diff','--name-only',args.measurement_root,'--',
            'ZesuSsz','InstrSpecs','ZesuStock'],text=True).strip():
        raise ValueError('The native source tree differs from the announced root')
    check_entry_bindings.validate_report(args.binding_report,args.design,root)
    baseline=load_baseline(args.baseline)
    selected=selection(baseline,args.all)
    design=json.loads(Path(args.design).read_text());cfg=json.loads(Path(args.cfg).read_text())
    historical=json.loads(Path(args.historical).read_text());full=json.loads(Path(args.full_on).read_text())
    states,errors=entry_schema.design_states(design,root,'ZesuSsz.Stock.Closure.index_decodeItem',['  decodeItemSelectedCode -∗'])
    ready,gaps=discovery.prepare(design,cfg,states,gen_block.address(design['entry_pc']),errors)
    if gaps or len(ready)!=24:
        raise ValueError('All24 executable entries must validate')
    reused_candidates={json.loads(Path(p).read_text())['entry_pc']:p for p in args.reuse_coqc}
    out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
    import sys
    sys.path.insert(0,str(root/'tools'))
    from coqc_recipe import remember_recipe
    if remember_recipe(Path(args.build_dir)) is None:
        raise ValueError('The focused build has no compiler recipe')
    jobs,reused,frozen=[],[],[]
    production_sources = {}
    for row,block,state in ready:
        state['imports']=list(dict.fromkeys(state['imports']+historical['probe_imports']+full['on_additions']+args.additional_import))
        rendered=successor_entailment.native_boundary_source(state,block,design,root,
            terminal=discovery.designed_terminal(block,{'workspace':str(root),'terminal':'decodeItemReturnAddress args'}))
        production_sources[row['entry_pc']] = rendered
        if not args.all:
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
    native_job_count=len(jobs)
    if args.profiles:
        if not args.all:
            raise ValueError('Prepared profiles require a fresh all-entry run')
        for profile in json.loads(args.profiles.read_text()):
            source=Path(profile['owned_source'])
            if coqc_primary.digest(source)!=profile['sha256']:
                raise ValueError('A prepared profile source changed')
            previous=json.loads(Path(profile['historical_source']).with_name('evidence.json').read_text())
            rendered={**previous,'source':source.read_text()}
            coqc_primary.instrument(rendered)
            jobs.append((rendered,out/'profiles'/profile['pc'],Path(args.build_dir),previous['inherited_debts']))
    inputs={str(Path(p).resolve()):coqc_primary.digest(p) for p in [args.baseline,args.full_on,args.historical,args.design,args.cfg,args.binding_report,
        __file__,production_modules.__file__,coqc_primary.__file__,coqc_primary.coqc_certificate.__file__,successor_entailment.__file__,chain_root.__file__,entry_schema.__file__,
        'tools/coqc_scratch.sh',str(Path(args.build_dir)/'coqc_recipe.json'),coqc_primary.chain_goals.__file__,
        '/home/cody/islaris/_opam/bin/coqc']}
    for tree in (root/'ZesuSsz/Automation',root/'ZesuSsz/Contracts',root/'InstrSpecs',root/'ZesuStock'):
        for path in tree.rglob('*.v'):
            inputs[str(path.resolve())]=coqc_primary.digest(path)
    for path in (Path(args.build_dir)/'default').rglob('*.vo'):
        inputs[str(path.absolute())]=coqc_primary.digest(path)
    if args.profiles:
        inputs[str(args.profiles.resolve())]=coqc_primary.digest(args.profiles)
        for profile in json.loads(args.profiles.read_text()):
            inputs[profile['owned_source']]=profile['sha256']
            metadata=Path(profile['historical_source']).with_name('evidence.json')
            inputs[str(metadata)]=coqc_primary.digest(metadata)
    import_targets=native_import_targets([rendered['source'] for rendered,_,_,_ in jobs],root)
    planned={'measurement_root':args.measurement_root,'inputs':inputs,'additional_imports':args.additional_import,
        'native_import_targets':import_targets,'proof_budget':default_policy,'module_limits':overrides,
        'native_jobs':native_job_count,'profile_jobs':len(jobs)-native_job_count,'sources':[]}
    for rendered,directory,_,debts in jobs:
        directory.mkdir(parents=True,exist_ok=True)
        native=directory/'Native.v'
        if native.exists() and native.read_text()!=rendered['source']:
            raise ValueError('A prepared native source changed')
        if not native.exists():
            native.write_text(rendered['source'])
        planned['sources'].append({'entry':rendered['entry_pc'],'source':str(native),
            'sha256':coqc_primary.digest(native),'statement_sha256':rendered['statement_sha256'],
            'instrumented_sha256':hashlib.sha256(coqc_primary.instrument(rendered,
                cpu_seconds=policy_for(rendered['entry_pc'])['cpu_seconds'],
                memory_gib=policy_for(rendered['entry_pc'])['memory_kib']//(1024*1024)).encode()).hexdigest(),
            'proof_budget':policy_for(rendered['entry_pc']),
            'inherited_debts':debts})
    input_path=out/'run-inputs.json'
    if input_path.exists() and json.loads(input_path.read_text())!=planned:
        raise ValueError('The prepared native inputs changed before execution')
    if not input_path.exists():
        input_path.write_text(json.dumps(planned,sort_keys=True)+'\n')
    if args.prepare_only:
        print(json.dumps({'preflight':str(input_path),'sha256':coqc_primary.digest(input_path),'native_jobs':native_job_count,'profile_jobs':len(jobs)-native_job_count}))
        return
    started=time.monotonic();before=discovery.machine()
    jobs = [(*job, policy_for(job[0]['entry_pc'])['cpu_seconds'],
                    policy_for(job[0]['entry_pc'])['memory_kib']//(1024*1024)) for job in jobs]
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        executed=list(pool.map(worker,jobs))
    for path,expected in inputs.items():
        if coqc_primary.digest(path)!=expected:
            raise ValueError('A fallback input changed during execution')
    result={'measurement_root':args.measurement_root,'checkout_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        'label':'Fresh actual designed successor attempts on announced automation' if args.all else 'Actual designed successor attempts; completed native baselines remain unchanged',
        'inputs':inputs,'workers':args.jobs,'elapsed_seconds':time.monotonic()-started,
        'machine_before':before,'machine_after':discovery.machine(),'new_coqc_attempts':native_job_count,
        'reused_coqc_attempts':len(reused),'unchanged_mcp_attempts':len(frozen),
        'coqc_results':reused+executed[:native_job_count],'profile_results':executed[native_job_count:],'unchanged_baseline':frozen,
        'prepared_inputs':{'path':str(input_path),'sha256':coqc_primary.digest(input_path)},
        'blocks_closed':sum(bool(r.get('block_closed')) for r in reused+executed[:native_job_count]),'contract_closures':0,
        'closure_policy':'Exact compiled native Qed, empty assumptions, and no inherited debts certify a block. Missing diagnostic groups do not certify closure.'}
    if args.emit_production:
        result['production_modules'] = emit_native_production(
            reused + executed[:native_job_count], production_sources, root)
        result['production_module_status'] = 'Emitted source; current production compilation and exact verification remain required'
    result['classes']=dict(collections.Counter([r['outcome'] for r in result['coqc_results']]+[r['outcome'] for r in frozen]))
    path=out/'report.json';path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'report':str(path),'sha256':coqc_primary.digest(path),'classes':result['classes'],'blocks_closed':result['blocks_closed']}))


if __name__=='__main__':
    main()
