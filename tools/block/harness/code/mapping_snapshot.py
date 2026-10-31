"""Reuse pinned coqdep answers after exact seed, parser, and file checks."""
from pathlib import Path
import hashlib,json


def digest(path):
    with Path(path).open('rb') as stream:return hashlib.file_digest(stream,'sha256').hexdigest()


def bound(row):
    path=Path(row['path'])
    if digest(path)!=row['sha256']:raise ValueError('A mapping snapshot binding changed.')
    return path


def rebase(path,old,new):
    path=Path(path)
    return Path(new)/path.relative_to(old) if path.is_relative_to(old) else path


def load(instance,binding,workspace,changes):
    snapshot=json.loads(bound(binding).read_text())
    if snapshot['schema']!='compiled-library.seed-snapshot.v1':raise ValueError('Unsupported mapping snapshot.')
    bound(snapshot['seed'])
    if instance.tool_sha256!=snapshot['resolver']['sha256']:raise ValueError('The mapping snapshot uses another coqdep.')
    import check_data_only_lemmas
    actual_parsers=[Path(__file__).with_name('installed_mappings.py'),Path(check_data_only_lemmas.__file__),Path(__file__)]
    if [digest(path) for path in actual_parsers]!=[row['sha256'] for row in snapshot['parsers']]:raise ValueError('The mapping snapshot parser identity differs.')
    for row in snapshot['parsers']:bound(row)
    old=Path(snapshot['workspace']);new=Path(workspace)
    expected=[dict(row,root=str(rebase(row['root'],old,new))) for row in snapshot['roots']]
    if instance.roots!=expected:raise ValueError('The mapping snapshot load paths differ.')
    if instance.flags!=[str(rebase(word,old,new)) if word.startswith('/') else word for word in snapshot['flags']]:raise ValueError('The mapping snapshot flags differ.')
    actual={str(row['object']):row for row in instance.entries}
    expected_objects={str(rebase(row['object']['path'],old,new)):row for row in snapshot['entries']}
    allowed={str(Path(path)):row for path,row in changes.items()}
    for path in set(actual)^set(expected_objects):
        source=str(Path(path).with_suffix('.v'))
        if source not in allowed:raise ValueError('The mapping snapshot object inventory changed.')
    # Every baseline object stays exact, except the explicitly bound caller/Rules pair.
    for path,row in expected_objects.items():
        source=str(rebase(row['source']['path'],old,new))
        if source in allowed:
            expected_change=allowed[source]
            if digest(source)!=expected_change['source_sha256']:raise ValueError('A changed mapping source differs from its authority.')
            if expected_change.get('object_sha256') is not None and (path not in actual or digest(path)!=expected_change['object_sha256']):raise ValueError('A changed Rules object differs from its prefix.')
            continue
        if path not in actual or digest(path)!=row['object']['sha256']:raise ValueError('An unchanged mapping object changed.')
        if row['source_present'] and (not Path(source).is_file() or digest(source)!=row['source']['sha256']):raise ValueError('An unchanged mapping source changed.')
    source_rows={str(rebase(row['source']['path'],old,new)):row for row in snapshot['sources']}
    current=sorted({entry['source'] for entry in instance.entries if entry['source'].is_file()})
    instance.scanned_sources=True
    parsed=0
    for source in current:
        row=source_rows.get(str(source));actual_hash=digest(source)
        if row is None or actual_hash!=row['source']['sha256']:
            if str(source) not in allowed:raise ValueError('An unlisted mapping source requires a new seed snapshot.')
            instance.register_source(source.read_text(),source);parsed+=1
            continue
        identity={'path':str(source),'sha256':actual_hash}
        for request in row['requests']:
            rows=instance.requests.setdefault(request['module'],[])
            if not any(value['statement']==request['statement'] for value in rows):rows.append({'statement':request['statement'],'origin':identity})
        instance.source_records[str(source)]={'source':identity,'requests':row['requests']}
    instance.seed_snapshot={'binding':binding,'value':snapshot,'old':old,'new':new,'parsed_changed_sources':parsed,'hits':0,'misses':0}


def answer(instance,module):
    state=instance.seed_snapshot
    if state is None:return None
    row=state['value']['resolutions'].get(module)
    requests=instance._find_request(module)
    if row is None or [request['statement'] for request in requests]!=row['requests']:
        state['misses']+=1;return None
    source=rebase(row['source']['path'],state['old'],state['new']);obj=rebase(row['object']['path'],state['old'],state['new'])
    entries=[entry for entry in instance.entries if entry['source']==source and entry['object']==obj and entry['canonical']==row['canonical']]
    if not entries or digest(source)!=row['source']['sha256'] or digest(obj)!=row['object']['sha256']:
        state['misses']+=1;return None
    state['hits']+=1
    return {'source':source,'object':obj,'canonical':row['canonical'],'requests':row['requests']}


def export(instance,seed,workspace,parsers):
    bound(seed)
    entries=[]
    for row in instance.entries:
        source=row['source'];obj=row['object'];exists=source.is_file()
        entries.append({'canonical':row['canonical'],'object':{'path':str(obj),'sha256':digest(obj)},'source':{'path':str(source),'sha256':digest(source) if exists else None},'source_present':exists})
    return {'schema':'compiled-library.seed-snapshot.v1','seed':seed,'workspace':str(workspace),'flags':instance.flags,'roots':instance.roots,'resolver':{'path':str(instance.coqdep),'sha256':instance.tool_sha256},'parsers':parsers,'entries':entries,'sources':list(instance.source_records.values()),'resolutions':{name:{'source':{'path':str(row['source']),'sha256':digest(row['source'])},'object':{'path':str(row['object']),'sha256':digest(row['object'])},'canonical':row['canonical'],'requests':row['requests']} for name,row in instance.resolutions.items()}}
