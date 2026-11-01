"""Release waiting references. Restore exact private data before continuation."""
from contextlib import contextmanager
from pathlib import Path
import gc
import hashlib
import json
import os
import stat
import time
import uuid

from entry_chain import save,strict_loads
from run_registry import identity


def release_optional_caches():
    """Call only at a quiescent validation or child-wait boundary."""
    from binding_cache import release_process_cache
    from proof_bindings import release_classification_cache
    from supplier_ready import release_validation_cache
    result={'digests':release_process_cache(),
            'classified_rows':release_classification_cache(),
            'supplier_entries':release_validation_cache()}
    gc.collect()
    return result


def file_identity(value):
    return (value.st_dev,value.st_ino,value.st_size,value.st_mtime_ns,
            value.st_ctime_ns,value.st_mode,value.st_uid,value.st_nlink)


def read_checkpoint(reference,owner):
    path=Path(reference['path']);before=path.lstat()
    if (path.resolve()!=path or not stat.S_ISREG(before.st_mode) or before.st_uid!=os.getuid()
            or stat.S_IMODE(before.st_mode)!=0o600 or before.st_nlink!=1):
        raise ValueError('The waiting checkpoint is not one private owned file.')
    if file_identity(before)!=tuple(reference['identity']):
        raise ValueError('The waiting checkpoint identity changed.')
    current=identity(os.getpid())
    if current is None or (current['pid'],current['startticks'])!=(owner['pid'],owner['startticks']):
        raise ValueError('The waiting checkpoint belongs to another controller.')
    with path.open('rb') as stream:
        if file_identity(os.fstat(stream.fileno()))!=file_identity(before):
            raise ValueError('The waiting checkpoint changed before reading.')
        raw=stream.read()
        if file_identity(os.fstat(stream.fileno()))!=file_identity(before):
            raise ValueError('The waiting checkpoint changed during reading.')
    if file_identity(path.lstat())!=file_identity(before):
        raise ValueError('The waiting checkpoint changed after reading.')
    if hashlib.sha256(raw).hexdigest()!=reference['sha256']:
        raise ValueError('The waiting checkpoint bytes changed.')
    value=strict_loads(raw.decode())
    if file_identity(path.lstat())!=tuple(reference['identity']):
        raise ValueError('The waiting checkpoint changed while decoding.')
    if (set(value)!={'schema','owner','objects'} or value['schema']!='controller.waiting-data.v1'
            or value['owner']!=owner or not isinstance(value['objects'],dict)):
        raise ValueError('The waiting checkpoint has another identity or schema.')
    return value['objects']


@contextmanager
def compact_wait(output,**objects):
    """Keep all data on disk. This context grants no validation authority."""
    if not objects or any(not isinstance(value,dict) for value in objects.values()):
        raise ValueError('A waiting envelope requires dictionary references.')
    if len({id(value) for value in objects.values()})!=len(objects):
        raise ValueError('A waiting envelope repeats one dictionary reference.')
    output=Path(output).absolute()
    if output.resolve()!=output or output.stat().st_uid!=os.getuid():
        raise ValueError('The waiting output directory is not canonical and owned.')
    directory=output/'waiting-envelopes'
    directory.mkdir(mode=0o700,parents=True,exist_ok=True)
    before=directory.lstat()
    if directory.resolve()!=directory or before.st_uid!=os.getuid() or stat.S_IMODE(before.st_mode)!=0o700:
        raise ValueError('The waiting envelope directory is not private and owned.')
    owner=identity(os.getpid());owner={'pid':owner['pid'],'startticks':owner['startticks'],'uid':os.getuid()}
    path=directory/(uuid.uuid4().hex+'.json')
    save(path,{'schema':'controller.waiting-data.v1','owner':owner,'objects':objects})
    with path.open('rb') as stream:sha=hashlib.file_digest(stream,'sha256').hexdigest()
    reference={'path':str(path),'sha256':sha,'identity':list(file_identity(path.lstat()))}
    report={'checkpoint':reference,'owner':owner,'object_names':sorted(objects),
            'started_ns':time.time_ns(),'restored':False}
    for name,value in objects.items():
        value.clear();value['waiting_envelope']={'checkpoint':json.loads(json.dumps(reference)),'object':name}
    try:
        report['released_caches']=release_optional_caches()
        yield json.loads(json.dumps(reference))
    finally:
        try:
            for name,value in objects.items():
                if value!={'waiting_envelope':{'checkpoint':reference,'object':name}}:
                    raise ValueError('A suspended dictionary changed during its wait.')
            restored=read_checkpoint(reference,owner)
            if set(restored)!=set(objects) or any(not isinstance(value,dict) for value in restored.values()):
                raise ValueError('The waiting checkpoint changed its dictionary set.')
            for name,value in objects.items():
                value.clear();value.update(restored[name])
            report['restored']=True
        except BaseException as error:
            report['restore_error']=type(error).__name__+': '+str(error)
            raise
        finally:
            report['ended_ns']=time.time_ns()
            save(path.with_suffix('.receipt.json'),report)
