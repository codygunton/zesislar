"""Resolve checked rollback references without changing event ownership."""
from trace_block_kernel_display import _exact

REUSE_FLAGS = {'exact', 'proofview_backtracked', 'interp_summary_restored',
               'synterp_summary_restored', 'evd_physical_equal', 'environment_physical_equal',
               'ordered_groups_equal', 'fresh_counter_equal'}


class ReferencedRollback:
    """Keep the source capture and expose the current rollback provenance."""
    def __init__(self, source, reference, event):
        self.source = source
        self.capture = source.capture
        self.catalog = source.catalog
        self.provenance = {'kind': 'checked-discarded-rollback-reference',
                           'event': dict(reference), 'event_sequence': event['sequence'],
                           'source_event': dict(event['capture_ref']['event']),
                           'source_sequence': event['capture_ref']['source_sequence'],
                           'reuse_check': dict(event['reuse_check'])}

    def stable(self):
        value = dict(self.source.stable())
        value['capture_provenance'] = self.provenance
        return value


def resolve_rollback_references(events, checked_captures):
    """The caller first validates every direct capture with its pinned reader."""
    captures = dict(checked_captures)
    references = {row['path']: row for row in events.references}
    for reference in events.references:
        event = events.read(reference)
        if 'capture_ref' not in event:
            continue
        expected = {'schema', 'sequence', 'kind', 'rule', 'invocation', 'trial',
                    'parent_invocation', 'clause', 'exact', 'capture_ref', 'reuse_check'}
        if (set(event) != expected or event['kind'] != 'hand-rollback'
                or event['trial'] is not False or event['exact'] is not True):
            raise ValueError('The capture reference is not an exact discarded rollback.')
        reuse, binding = event['reuse_check'], event['capture_ref']
        if (not isinstance(reuse, dict) or set(reuse) != REUSE_FLAGS | {'kind'}
                or reuse['kind'] != 'discarded-branch-rollback'
                or any(reuse[key] is not True for key in REUSE_FLAGS)):
            raise ValueError('The rollback reference lacks its complete reuse checks.')
        if not isinstance(binding, dict) or set(binding) != {'event', 'capture', 'source_sequence'}:
            raise ValueError('The rollback reference has unsupported source fields.')
        source_reference = binding['event']
        if (not isinstance(source_reference, dict) or set(source_reference) != {'path', 'sha256', 'bytes'}
                or type(source_reference['bytes']) is not int or source_reference['bytes'] < 0
                or type(binding['source_sequence']) is not int
                or not 0 < binding['source_sequence'] < event['sequence']):
            raise ValueError('The rollback reference lacks its exact prior source identity.')
        source_file = references.get(source_reference['path'])
        if (source_file is None or source_file != {key: source_reference[key] for key in ('path', 'sha256')}
                or (events.root / source_reference['path']).stat().st_size != source_reference['bytes']):
            raise ValueError('The rollback source leaves its sealed owned stream.')
        source = events.read(source_file)
        if (source['kind'] != 'native-entry' or source.get('trial') is not False
                or 'capture' not in source or 'capture_ref' in source
                or source['sequence'] != binding['source_sequence']
                or not _exact(binding['capture'], source['capture'])
                or any(not _exact(source.get(key), event[key]) for key in
                       ('rule', 'invocation', 'parent_invocation'))):
            raise ValueError('The rollback source is not its exact direct native entry.')
        number = source['sequence']
        checked = checked_captures.get(number)
        if (checked is None or checked.capture.get('event_sequence') != number
                or not _exact(getattr(checked, 'event_reference', None), source_file)
                or not _exact(getattr(checked, 'capture_envelope', None), source['capture'])
                or not _exact(getattr(checked, 'owned_process', None), events.process)):
            raise ValueError('The rollback source has no independently checked complete capture.')
        if event['sequence'] in captures:
            raise ValueError('The rollback reference conflicts with a direct capture.')
        captures[event['sequence']] = ReferencedRollback(checked, reference, event)
    return captures
