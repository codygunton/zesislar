"""Keep a declaration distinct from commands before its Proof sentence."""
from pathlib import Path
from residual.modules import parse_module
from check_data_only_lemmas import rocq_commands,rocq_tokens

def source_statement(path, expected_body='zesu_block.'):
    from native_route import body
    body(expected_body)
    text=Path(path).read_text();lines=text.splitlines(keepends=True)
    proofs=[p for p in parse_module(Path(path)) if p.name.startswith('DesignedBoundary_')]
    if len(proofs)!=1 or proofs[0].inline:raise ValueError('The native source needs one separate boundary proof.')
    proof=proofs[0]
    if ''.join(proof.body).strip()!=expected_body:raise ValueError('The native body changed.')
    start=sum(map(len,lines[:proof.declaration_line]));proof_start=sum(map(len,lines[:proof.proof_line]))
    commands=[c for c in rocq_commands(text) if c and c[0][1]==start]
    if len(commands)!=1:raise ValueError('The native declaration boundary is ambiguous.')
    last,offset=commands[0][-1];tail=offset+len(last);stop=rocq_tokens(text[tail:])[0]
    if stop[0]!='.':raise ValueError('The declaration lacks its command terminator.')
    end=tail+stop[1]+1
    while end<len(text) and text[end] in ' \t':end+=1
    if end<len(text) and text[end]=='\n':end+=1
    between=text[end:proof_start]
    for command in rocq_commands(between):
        words=[v for v,_ in command]
        if not words or 'Require' not in words or words[0] not in {'Require','From'}:
            raise ValueError('An unsupported command separates the statement and Proof.')
    return {'name':proof.name,'prefix':text[:start],'statement':text[start:end],
            'pre_proof_commands':between,'native_body':expected_body}


def compiled_verification(runtime,target,source,specification,name,*,workspace,manager,receipt):
    """Restate an exact declaration with its authenticated compiled identities."""
    import hashlib,re
    from entry_chain import binding
    from binding_cache import force_hashing
    from compiler_snapshot import accepted_objects,producer
    module=target['module']
    identifier=r"[A-Za-z_][A-Za-z0-9_']*"
    if (not isinstance(module,str) or re.fullmatch(identifier+r'(?:\.'+identifier+r')*',module) is None
            or re.fullmatch(identifier,name) is None):
        raise ValueError('The verification module or theorem name is invalid.')
    source=Path(source);workspace=Path(workspace).resolve()
    selected=Path(runtime['module_files'][module])
    if selected.is_absolute() or '..' in selected.parts or (workspace/selected).resolve()!=source.resolve():
        raise ValueError('The verification source differs from its module mapping.')
    if not source.resolve().is_relative_to(workspace):
        raise ValueError('The verification source leaves its owned workspace.')
    current=source_statement(source,specification['native_body'])
    if current!=specification or hashlib.sha256(current['statement'].encode()).hexdigest()!=target['statement_sha256']:
        raise ValueError('The original verification declaration changed.')
    allowed={'Require','From','Import','Export','Record','Inductive','CoInductive','Definition','Ltac','Ltac2'}
    original_imports=[]
    context=current['prefix']+current['pre_proof_commands']
    for command in rocq_commands(context):
        if (not command or command[0][0] not in allowed
                or command[0][0]=='From' and not any(word=='Require' for word,_ in command)):
            raise ValueError('The verification prefix contains unsupported local syntax.')
        if command[0][0] in {'Require','From','Import','Export'}:
            last,offset=command[-1];tail=offset+len(last)
            stop=rocq_tokens(context[tail:])[0]
            if stop[0]!='.':raise ValueError('A verification import lacks its command terminator.')
            original_imports.append(context[command[0][1]:tail+stop[1]+1]+'\n')
    words=rocq_tokens(current['statement'])
    if (len(words)<2 or words[0][0]!='Lemma' or words[1][0]!=current['name']
            or re.fullmatch(identifier,current['name']) is None):
        raise ValueError('The verification declaration is unsupported.')
    if manager is None or not isinstance(receipt,dict) or receipt not in manager.rows:
        raise ValueError('The verification lacks its accepted compilation receipt.')
    compiler=runtime.get('physical_compiler')
    reference={'path':runtime['runtime_path'],'sha256':runtime['runtime_sha256']}
    if (not isinstance(compiler,dict) or manager.snapshot['runtime']!=reference
            or manager.snapshot['producer']!=producer()
            or any(manager.snapshot['compiler'][key]!=compiler[key] for key in ['path','sha256'])):
        raise ValueError('The verification compiler or producer differs from its receipt.')
    with force_hashing(True):
        source_binding=binding(source);object_binding=binding(source.with_suffix('.vo'))
        if source_binding['sha256']!=target['source_sha256'] or binding(Path(compiler['path']))!=compiler:
            raise ValueError('The verification source or compiler bytes changed.')
        _,_,receipts,objects=accepted_objects(manager.snapshot,manager.reference,manager.key,
                                              compiler,runtime['physical_flags'])
        matches=[row for row in objects if row['kind']=='vo' and row['receipt']==receipt
                 and row['source']==source_binding and row['path']==object_binding['path']
                 and row['sha256']==object_binding['sha256']]
        if receipt not in receipts or len(matches)!=1:
            raise ValueError('The verification object differs from its accepted source receipt.')
        if binding(source)!=source_binding or binding(source.with_suffix('.vo'))!=object_binding:
            raise ValueError('A verification input changed during payload construction.')
    start=words[1][1];stop=start+len(current['name'])
    declaration=current['statement'][:start]+name+current['statement'][stop:]
    imports=''.join(original_imports)+'Require Import '+module+'.\n'
    problem=imports+declaration
    proof=problem+'Proof. apply '+module+'.'+current['name']+'. Qed.\n'
    return {'problem_statement':problem,'proof':proof,'problem_name':name,
            'context':{'module':module,'source':source_binding,'object':object_binding,
                       'compiler':compiler,'accepted_compilation':receipt,
                       'original_statement_sha256':target['statement_sha256']}}
