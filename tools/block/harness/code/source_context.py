"""Preserve the global load path while matching stock Sail compilation context."""
import hashlib
from pathlib import Path


def compilation(flags, source):
    """Derive physical flags only from one unchanged bound source and mapped root."""
    if (not isinstance(source, dict) or set(source) != {'path', 'sha256'}
            or not isinstance(source['path'], str) or not isinstance(source['sha256'], str)):
        raise ValueError('The compiler source context lacks an exact source binding.')
    path = Path(source['path'])
    selected = path.resolve()
    original, effective = list(flags), list(flags)
    roots = []
    index = 0
    while index < len(original):
        flag = original[index]
        if flag in {'-Q', '-R'}:
            if index + 2 >= len(original):
                raise ValueError('The compiler source mapping is incomplete.')
            root = Path(original[index + 1]).resolve()
            if original[index + 2] == 'SailStdpp' and selected.is_relative_to(root):
                roots.append((index, root, flag))
            index += 3
        else:
            index += 1
    if len({root for _, root, _ in roots}) > 1:
        raise ValueError('The compiler source belongs to conflicting Sail mappings.')
    if roots:
        with path.open('rb') as stream:
            actual = hashlib.file_digest(stream, 'sha256').hexdigest()
        if actual != source['sha256']:
            raise ValueError('The compiler source context changed.')
    changes = []
    for index, root, flag in roots:
        if flag == '-Q':
            effective[index] = '-R'
            changes.append({'index': index, 'root': str(root), 'prefix': 'SailStdpp',
                            'before': '-Q', 'after': '-R'})
    return {'schema': 'entry-chain.source-context.v1', 'source': dict(source),
            'base_flags': original, 'physical_flags': effective, 'changes': changes}


def effective_flags(flags, source):
    return compilation(flags, source)['physical_flags']
