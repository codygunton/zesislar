import sys,os
from pathlib import Path
sys.dont_write_bytecode=True
os.environ['PYTHONDONTWRITEBYTECODE']='1'
directory=Path(__file__).resolve().parent
if directory.name=='block':
    if directory.parent.name!='tools':raise ValueError('The compiler lacks its owned tools directory.')
    sys.path.insert(1,str(directory.parent))
import clone_copy
"""Validate MCP arguments and preserve the bound physical compiler vector."""
import os
from pathlib import Path
import sys
import uuid
from entry_chain import binding,digest,read_bound,save
from entry_chain_resources import normalize_cpu,check_operation


def validated_arguments(args,expected,workspace):
    if not args or args[:len(expected)]!=expected:
        raise ValueError('The MCP compiler flag vector differs from the bound project.')
    tail=args[len(expected):]
    if len(tail)==1:
        source=Path(tail[0]).resolve();extra=[]
    elif len(tail)==3 and tail[0]=='-o':
        source=Path(tail[2]).resolve();output=Path(tail[1]).resolve()
        if not output.is_relative_to(workspace) or output.suffix not in {'.vo','.vos'}:
            raise ValueError('The MCP object output leaves its owned workspace.')
        extra=['-o',str(output)]
    else:
        raise ValueError('The MCP compiler adds an unexpected option.')
    if not source.is_relative_to(workspace) or source.suffix!='.v' or not source.is_file():
        raise ValueError('The MCP compiler source leaves its owned workspace.')
    return source,extra


def main():
    normalize_cpu()
    runtime_reference={'path':os.environ['ENTRY_CHAIN_RUNTIME_JSON'],
                       'sha256':os.environ['ENTRY_CHAIN_RUNTIME_SHA256']}
    runtime=read_bound(runtime_reference)
    workspace=Path(os.environ['ROCQ_WORKSPACE']).resolve()
    source,extra=validated_arguments(sys.argv[1:],runtime['expected_mcp_flags'],workspace)
    physical='/home/cody/islaris/_opam/bin/coqc'
    snapshot_path=os.environ.get('ENTRY_CHAIN_COMPILER_SNAPSHOT_JSON')
    snapshot_sha=os.environ.get('ENTRY_CHAIN_COMPILER_SNAPSHOT_SHA256')
    if bool(snapshot_path)!=bool(snapshot_sha):
        raise ValueError('The compiler snapshot binding is incomplete.')
    validation=None
    if snapshot_path:
        if not os.environ.get('ENTRY_CHAIN_COMPILER_SNAPSHOT_OUTPUT_KEY'):
            raise ValueError('The compiler lacks its authenticated output context.')
        validation={'snapshot':{'path':snapshot_path,'sha256':snapshot_sha},
                    'runtime':runtime_reference}
    else:
        check_operation(runtime)
    flags=runtime['physical_flags']
    directory=Path(runtime['job_output'])/'compiler-invocations'/uuid.uuid4().hex
    directory.mkdir(parents=True)
    clone_copy.copy2(source,directory/'SOURCE.v')
    command=[physical,*flags,*extra,str(source)]
    selected=runtime.get('target',{}).get('block') or {}
    module=next((name for name,rel in runtime['module_files'].items() if (workspace/rel).resolve()==source),'unmapped-verification')
    import re
    found=re.search(r'^(?:Lemma|Theorem)\s+(\w+)',source.read_text(),re.M)
    theorem=found.group(1) if found else 'module-compilation'
    native=(runtime['phase']=='native' and module==selected.get('module'))
    phase='native_compile' if native else ('verification' if runtime['phase']=='native' else 'setup')
    save(directory/'INPUT.json',{'incoming_argv':sys.argv[1:],'physical_argv':command,
         'source':binding(source),'retained_source':binding(directory/'SOURCE.v'),
         'compiler':binding(physical),'validation':validation,'CPU_policy':'unlimited','owned_workspace':str(workspace),
         'target':{'module':module,'theorem':theorem,'source_sha256':digest(source)},'command_phase':phase})

    wrapper=workspace/'tools/coqc_findlib.py';guard=workspace/'tools/resource_guard.sh'
    os.execv(sys.executable,[sys.executable,'-B',str(wrapper),'guarded','--guard',str(guard),'--',sys.executable,'-B',str(Path(__file__).with_name('compile_measure.py')),str(directory)])


if __name__=='__main__':main()
