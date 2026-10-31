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
