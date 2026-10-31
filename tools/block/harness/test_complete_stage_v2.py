"""Exercise complete stage_job with real inputs and no proof/compiler launch."""
from pathlib import Path
from copy import deepcopy
from unittest.mock import patch
import argparse
import hashlib
import json
import subprocess
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE/'code')]
import scratch
import dependency_batch
import entry_chain_run

def bind(path):
    path=Path(path).resolve()
    return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--runtime',type=Path,required=True)
    parser.add_argument('--runtime-sha256',required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    assert bind(args.runtime)['sha256']==args.runtime_sha256
    config=json.loads(args.runtime.read_text())
    assert config['declarations_only']
    assert not any(Path(row['output']).exists() for row in config['jobs'])
    job=deepcopy(config['jobs'][0])
    policy=deepcopy(config['admission'])
    policy.update(claim_key='nonproof-stage-only',minimum_claim_bytes=job['claim_bytes'],
        physical_fence_bytes=job['physical_fence_bytes'],memory_job=deepcopy(job))
    job['policy']=policy
    output=args.output.resolve();output.mkdir(exist_ok=False)
    observed=[]
    real_run=subprocess.run
    def run_only_import_probe(argv,*arguments,**options):
        assert Path(argv[0]).resolve()==Path(sys.executable).resolve(),argv
        assert argv[1:3]==['-B','-c'],argv
        observed.append(argv)
        return real_run(argv,*arguments,**options)
    with patch.object(entry_chain_run.subprocess,'run',side_effect=run_only_import_probe):
        runtime,workspace=entry_chain_run.stage_job(config,job,output)
    ordinary=workspace/'tools/block/compile_measure.py'
    dependency=workspace/'tools/block/dependency_compile_measure.py'
    assert bind(ordinary)['sha256']==bind(HERE/'code/compile_measure.py')['sha256']
    assert bind(dependency)['sha256']=='bb54ce6bc73f6841ce2caeb53dfb8c0e3d6dd1eb782bb4f166ab1a8d3a5ea609'
    assert bind(ordinary)['sha256']!=bind(dependency)['sha256']
    dependency_batch.validate(runtime,workspace,job['ordered_modules'],runtime['dependency_batch'])
    assert not (output/'native/CALLS.json').exists()
    assert not (output/'STARTED.json').exists()
    result={'status':'complete_stage_job_passed_nonproof',
        'source_runtime':bind(args.runtime),'staged_runtime':bind(output/'RUNTIME.json'),
        'ordinary_recorder':bind(ordinary),'dependency_recorder':bind(dependency),
        'copy_receipts':bind(output/'COPIES.json'),
        'tool_transition':(bind(output/'RESTART-TOOLS-TRANSITION.json')
                           if (output/'RESTART-TOOLS-TRANSITION.json').is_file() else None),
        'prepared_tool_installation':bind(args.runtime.parent/'RECOVERY-TOOLS.json'),
        'Python_import_probe_calls':len(observed),'other_subprocess_calls':0,
        'module_order':job['ordered_modules'],'dependency_validator_passed':True,
        'guard':bind(workspace/'tools/resource_guard.sh'),
        'proof_calls':0,'compiler_calls':0,'claims_created':0,
        'qualification':'This test stages data only. Its synthetic policy must never execute.'}
    path=output/'STAGE-TEST-RESULT.json';path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(bind(path)),flush=True)

if __name__=='__main__':main()
