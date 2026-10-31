"""Attach an exact owned source to selected helper prerequisites."""
from copy import deepcopy
import hashlib
from pathlib import Path, PurePosixPath

try:
    from .entry_schema import source_module
except ImportError:
    from entry_schema import source_module


def _binding(*, workspace, relative_path, logical_module, predicate, original_source, expected_sha256):
    relative = PurePosixPath(relative_path)
    if (relative.is_absolute() or '..' in relative.parts or relative.suffix != '.v'
            or str(relative) != relative_path):
        raise ValueError('The owned source path must be a canonical relative .v path')
    if source_module(relative_path) != logical_module or predicate.rsplit('.', 1)[0] != logical_module:
        raise ValueError('The predicate owner and owned source path do not match')
    original = Path(original_source).resolve()
    if original.parts[-len(relative.parts):] != relative.parts:
        raise ValueError('The original source path does not match the bound logical module')
    if hashlib.sha256(original.read_bytes()).hexdigest() != expected_sha256:
        raise ValueError('The original source bytes differ from the bound hash')
    root = Path(workspace).resolve()
    owned = (root / relative_path).resolve()
    if not owned.is_relative_to(root):
        raise ValueError('The owned source path leaves its workspace')
    return original, owned


def copy_owned_source(*, workspace, relative_path, logical_module, predicate,
                      original_source, expected_sha256):
    """Copy verified bytes. Refuse an existing copy with different bytes."""
    original, owned = _binding(workspace=workspace, relative_path=relative_path,
        logical_module=logical_module, predicate=predicate, original_source=original_source,
        expected_sha256=expected_sha256)
    data = original.read_bytes()
    if owned.exists():
        if owned.read_bytes() != data:
            raise ValueError('The existing owned source has conflicting bytes')
    else:
        owned.parent.mkdir(parents=True, exist_ok=True)
        owned.write_bytes(data)
    return {'original_source': str(original), 'owned_source': str(owned),
            'relative_path': relative_path, 'logical_module': logical_module,
            'predicate': predicate, 'sha256': expected_sha256}


def _uses_predicate(components, predicate):
    for component in components:
        if (component.get('kind') in {'application', 'base', 'continuation'}
                and component.get('predicate') == predicate):
            return True
        if component.get('kind') == 'pure':
            for term in component.get('terms', []):
                origin = term.get('provenance', {})
                if origin.get('kind') == 'data' and origin.get('source') == predicate:
                    return True
        if component.get('kind') == 'disjunction' and _uses_predicate(component['alternatives'], predicate):
            return True
    return False


def attach_helper_source(profile, *, entry_pc, workspace, relative_path,
                         logical_module, predicate, original_source, expected_sha256):
    """Return a profile copy and a receipt. Keep every resource term unchanged.

    Only helpers that directly apply predicate or name it as data provenance
    receive this prerequisite. The author and shared source policies stay intact.
    """
    original, owned = _binding(workspace=workspace, relative_path=relative_path,
        logical_module=logical_module, predicate=predicate, original_source=original_source,
        expected_sha256=expected_sha256)
    if not owned.is_file() or hashlib.sha256(owned.read_bytes()).hexdigest() != expected_sha256:
        raise ValueError('The owned source bytes differ from the bound hash')
    rows = [(index, row) for index, row in enumerate(profile['design']['blocks']) if row['entry_pc'] == entry_pc]
    if len(rows) != 1:
        raise ValueError('The source supplement needs one selected entry row')
    index, row = rows[0]
    selected = []
    for auxiliary_index, auxiliary in enumerate(row['support']['additional_definitions']):
        declaration = auxiliary['declaration']
        if not _uses_predicate(declaration['support']['components'], predicate):
            continue
        hashes = declaration['source_hashes']
        if relative_path in hashes and hashes[relative_path] != expected_sha256:
            raise ValueError('The helper has a conflicting source hash')
        for path in hashes:
            if source_module(path) == logical_module and path != relative_path:
                raise ValueError('The helper binds the owner through a different source path')
        selected.append(auxiliary_index)
    if not selected:
        raise ValueError('No selected helper directly applies the source predicate')
    result, attachments = deepcopy(profile), []
    changed_row = result['design']['blocks'][index]
    for auxiliary_index in selected:
        declaration = changed_row['support']['additional_definitions'][auxiliary_index]['declaration']
        added = relative_path not in declaration['source_hashes']
        declaration['source_hashes'][relative_path] = expected_sha256
        attachments.append({'entry_definition': declaration['entry_definition'],
            'profile_path': ['design', 'blocks', index, 'support', 'additional_definitions',
                             auxiliary_index, 'declaration', 'source_hashes', relative_path],
            'added': added})
    receipt = {'schema': 'helper-source-attachment.v1', 'entry_pc': entry_pc,
        'original_source': str(original), 'owned_source': str(owned),
        'relative_path': relative_path, 'logical_module': logical_module,
        'predicate': predicate, 'sha256': expected_sha256, 'attachments': attachments,
        'resource_terms_changed': False, 'compact_author_changed': False,
        'shared_policies_changed': False, 'proof_ran': False}
    return result, receipt
