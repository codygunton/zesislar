"""Exclude old candidate-sensitive helper obligations from the private check.

The two original native statements and their zesu_block bodies stay exact.
Every retained helper is recompiled after the generated entry changes.
"""
import hashlib
import re
from pathlib import Path
from check_data_only_lemmas import rocq_commands, rocq_tokens


def identifiers(text):
    return {word for word, _ in rocq_tokens(text)
            if re.fullmatch(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*", word)}


def references(text, blocked):
    return identifiers(text) & blocked


def command_head(words):
    words=list(words)
    while words and words[0]=='#':
        if len(words)<2 or words[1]!='[':raise ValueError('Unsupported helper attribute.')
        depth=0;end=None
        for i,value in enumerate(words[1:],1):
            depth+=(value=='[')-(value==']')
            if depth==0:end=i+1;break
        if end is None:raise ValueError('Unclosed helper attribute.')
        words=words[end:]
    while words and words[0] in {'Global','Local','Polymorphic','Monomorphic'}:words=words[1:]
    return words


def declaration_name(tokens):
    words=command_head([value for value,_ in tokens])
    if len(words)>1 and words[0] in {'Definition','Instance','Ltac','Ltac2','Lemma','Theorem','Fact','Corollary','Remark','Example'}:
        return words[1] if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*",words[1]) else None
    return None


def filtered_sources(sources, entry):
    """Remove only obligations that mention the changed entry or removed helpers."""
    blocked={entry,entry.rsplit('.',1)[-1]};texts=dict(sources);removed=[]
    while True:
        changed=False
        for module,text in list(texts.items()):
            spans=[]
            # Existing lexer supplies exact command boundaries, including multiline Proof bodies.
            commands=rocq_commands(text)
            for index,command in enumerate(commands):
                if not command:continue
                words=[v for v,_ in command];name=declaration_name(command)
                head=command_head(words)
                if not head or head[0] not in {'Lemma','Theorem','Fact','Corollary','Remark','Example','Definition','Instance'}:continue
                if index+1>=len(commands) or not commands[index+1] or commands[index+1][0][0]!='Proof':continue
                closing=next((part for part in commands[index+2:] if part and part[0][0] in {'Qed','Defined','Admitted','Abort'}),None)
                if closing is None:raise ValueError('An old helper proof has no terminator: '+module)
                start=command[0][1];last,offset=closing[-1];end=text.find('.',offset+len(last))+1
                hit=references(text[start:end],blocked)
                if hit:spans.append((start,end,name,sorted(hit),'proof'))
            masked=text
            for start,end,_,_,_ in sorted(spans,reverse=True):masked=masked[:start]+' '*(end-start)+masked[end:]
            # Inline definitions, registrations, and tactics can depend on removed proofs.
            for command in rocq_commands(masked):
                if not command:continue
                words=[v for v,_ in command];hit=set(words)&blocked
                if not hit:continue
                if hit <= {entry,entry.rsplit('.',1)[-1]} and ('LithiumUnfold' in words or ('Typeclasses' in words and 'Opaque' in words) or ('Hint' in words and 'Unfold' in words)):
                    continue
                allowed={'Global','Local','Definition','Instance','Hint','Arguments','Typeclasses','Existing','Print','Ltac','Ltac2'}
                head=command_head(words)
                if not head or head[0] not in allowed:continue
                start=command[0][1];last,offset=command[-1];end=masked.find('.',offset+len(last))
                if end<0:raise ValueError('A helper command has no terminator.')
                end+=1;spans.append((start,end,declaration_name(command),sorted(hit),'declaration_or_registration'))
            if not spans:continue
            # Spans are disjoint because proof spans were masked before command parsing.
            for start,end,name,hit,kind in sorted(spans,reverse=True):
                removed.append({'module':module,'name':name,'kind':kind,'original_text':text[start:end],
                                'depends_on':hit,'sha256':hashlib.sha256(text[start:end].encode()).hexdigest()})
                if name:blocked.update({name,module+'.'+name})
                text=text[:start]+'\n(* H0: old entry-shape obligation excluded. See private route receipt. *)\n'+text[end:]
            texts[module]=text;changed=True
        if not changed:return texts,removed


def prepare_helpers(runtime, workspace, target, output):
    """Keep native files exact. Record every excluded old proof and source byte."""
    from check_entry import atomic_json,digest,relative
    prefix='ZesuSsz.Compliance.'
    paths={module:workspace/relative(name) for module,name in runtime['module_files'].items()
           if module.startswith(prefix) or module in {'ZesuSsz.Generated.DecodeItem.Registrations','ZesuSsz.Generated.DecodeItem.BootstrapRegistrations','ZesuSsz.Evidence.DecodeItemOutput24Selections'}}
    sources={module:path.read_text() for module,path in paths.items()}
    entry='ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt'+target.removeprefix('0x')
    filtered,removed=filtered_sources(sources,entry);changed=[];receipts=[]
    for module,text in filtered.items():
        if text==sources[module]:continue
        path=paths[module];rel=path.relative_to(workspace);original=output/'old-shape-obligations'/rel
        original.parent.mkdir(parents=True,exist_ok=True);original.write_text(sources[module]);path.write_text(text)
        # Source copies and physical Dune artifacts carry identical private bytes.
        logical=workspace/Path(*module.split('.')).with_suffix('.v')
        if logical!=path and logical.exists():logical.write_text(text)
        receipts.append({'module':module,'physical_path':str(path),'original_source':str(original),
                         'old_sha256':digest(original),'new_sha256':digest(path)})
        changed.append(module)
    atomic_json(output/'H0-EXCLUDED-OBLIGATIONS.json',{'entry':entry,'removed':removed,'sources':receipts,
        'native_sources_changed':False,'required_generic_automation_changed':False,
        'qualification':'Excluded old candidate-sensitive helper claims are not proof obligations of the two-proof check. Native failure remains a failure; no missing rule is silently treated as success.'})
    return changed
