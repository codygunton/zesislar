"""Project schema2 selected entries without materializing capture trees."""

from collections import defaultdict
from pathlib import Path

from trace_block_chunks import ChunkReader
from trace_block_stream import ReplayList


def stable_capture_lazy(capture):
    """Preserve the legacy stable shape through repeatable lazy arrays."""
    notation, plain = capture['notation'], capture['no_notation']

    def context(left, right):
        def rows():
            if len(left) != len(right):
                raise ValueError("The capture printers returned different context lengths.")
            for a, b in zip(left, right):
                if a['names'] != b['names']:
                    raise ValueError("The capture printers returned different context names.")
                yield {'names': a['names'], 'type': a['type'], 'type_nonotation': b['type'],
                       'body': a['body'], 'body_nonotation': b['body']}
        return ReplayList(rows)

    def goals(name):
        def rows():
            left, right = notation[name], plain[name]
            if len(left) != len(right):
                raise ValueError("The capture printers returned different goal counts.")
            for a, b in zip(left, right):
                if a['evar'] != b['evar']:
                    raise ValueError("The capture printers returned different goal identities.")
                yield {'id': a['evar'], 'goal': a['conclusion'], 'goal_nonotation': b['conclusion'],
                       'hyps': context(a['hyps'], b['hyps'])}
        return ReplayList(rows)

    def entries():
        left, right = notation['evars'], plain['evars']
        if len(left) != len(right):
            raise ValueError("The capture printers returned different Evd counts.")
        for a, b in zip(left, right):
            if a['evar'] != b['evar'] or a['defined'] != b['defined']:
                raise ValueError("The capture printers returned different Evd identities or status.")
            row = {'id': a['evar'], 'name': a['name'],
                   'status': 'defined' if a['defined'] else 'undefined',
                   'type': a['type'], 'type_nonotation': b['type'],
                   'context': context(a['hyps'], b['hyps']),
                   'body': a['body'], 'body_nonotation': b['body'], 'filter': a['filter']}
            if a['defined']:
                row['type_source'] = a['type_source']
            else:
                row.update(candidates=a['candidates'], candidates_nonotation=b['candidates'])
            yield row
    current = goals('goals')
    primary = current[0] if current else None
    return {'goal': primary['goal'] if primary else None,
            'goal_nonotation': primary['goal_nonotation'] if primary else None,
            'hyps': primary['hyps'] if primary else [], 'current_goals': current,
            'shelf': goals('shelf'), 'given_up': goals('given_up'),
            'evars': {'availability': 'complete', 'entries': ReplayList(entries),
                      'show_existentials': plain['show_existentials'],
                      'metadata_limit': 'Entry contexts, types, bodies, status, filters and candidates are retained. Universe constraints, source locations, relevance and abstraction metadata are not serialized.'},
            'hidden_focus_frames': notation['hidden_stack'],
            'completeness': {'required_fields_complete': True, 'missing_observations': []}}


class FilteredPoints:
    """Keep actual entries, their exact trials and their original snapshots.

    The caller supplies already verified schema2 metadata and process-bound
    references. Session closure and complete stream coverage remain separate.
    """

    def __init__(self, events, descriptors, session_id, index_dir):
        self.events, self.descriptors, self.session_id = events, descriptors, session_id
        self.index_dir = Path(index_dir)
        self.index_dir.mkdir(parents=True, exist_ok=True)
        self.documents = {}
        self.by_invocation = defaultdict(list)
        self.snapshot_rows = {}
        self.native = []
        clients = {}
        for reference in events.references:
            row = events.read(reference)
            # Validate all payloads before filtering feedback or reporting a
            # complete point. A match may otherwise stop a string scan early.
            for field in ('capture', 'message', 'refusal'):
                if field in row:
                    ChunkReader(events.root).validate(row[field], 'event-%08d/%s' % (row['sequence'], field))
            number = row.get('invocation')
            if row['kind'] in ('native-entry', 'hand-accepted', 'hand-rollback', 'hand-refused', 'feedback'):
                if type(number) is not int or number <= 0:
                    raise ValueError("A captured event lacks its exact invocation.")
            self.by_invocation[number].append((reference, row))
            if row['kind'] == 'native-entry' and row.get('trial') is False:
                client = row.get('rule')
                if client not in descriptors:
                    raise ValueError("A selected entry lacks its source-bound descriptor.")
                if number in clients:
                    raise ValueError("A native invocation repeats its entry identity.")
                clients[number] = client
                self.native.append((reference, row))
                self.snapshot_rows['invocation-%d:entry' % number] = reference
            elif row['kind'] in ('hand-accepted', 'hand-rollback'):
                if clients.get(number) != row.get('rule'):
                    raise ValueError("A hand trial differs from its native entry client.")
                clause = row.get('clause')
                if not isinstance(clause, str) or clause not in descriptors[clients[number]]['commands']:
                    raise ValueError("A hand trial lacks its source-bound command.")
                expected_trial = row['kind'] == 'hand-accepted'
                if row.get('trial') is not expected_trial:
                    raise ValueError("A hand trial lacks exact trial attribution.")
                suffix = 'after' if row['kind'] == 'hand-accepted' else 'rollback'
                key = 'invocation-%d:clause-%s:' % (number, clause)
                if key + suffix in self.snapshot_rows:
                    raise ValueError("A hand trial repeats its snapshot identity.")
                self.snapshot_rows[key + suffix] = reference
                if suffix == 'rollback':
                    self.snapshot_rows.setdefault(key + 'after', reference)

    def close(self):
        for document in self.documents.values():
            document.close()

    def __enter__(self):
        return self

    def __exit__(self, *arguments):
        self.close()

    def _capture(self, reference):
        name = reference['path']
        if name not in self.documents:
            sequence = self.events.read(reference)['sequence']
            self.documents[name] = self.events.open_capture(reference, self.index_dir / ('event-%08d.sqlite' % sequence))
        return stable_capture_lazy(self.documents[name].root)

    @property
    def snapshot_keys(self):
        return tuple(self.snapshot_rows)

    def get_snapshot(self, key):
        return self._capture(self.snapshot_rows[key])

    @staticmethod
    def _pointer(key):
        return '#/snapshots/' + key.replace('~', '~0').replace('/', '~1')

    def iter_points(self):
        for reference, entry in self.native:
            client, number = entry['rule'], entry['invocation']
            descriptor = self.descriptors[client]
            point = self._capture(reference)
            point.update(session_id=self.session_id,
                         trigger={'kind': 'rule-entry', 'rule': descriptor['rule'], 'client': client,
                                  'invocation': number, 'branch_status': []},
                         hint_log={'availability': 'complete', 'filter': descriptor['log_filter'],
                                   'selection': 'Keep invocation-attributed Debug messages and listed class/hint messages. Label liShow trial feedback separately.',
                                   'events': []}, hand_call=[], refusal=[])
            accepted = {}
            completed = set()
            feedback = defaultdict(list)
            for ref, row in self.by_invocation[number]:
                kind = row['kind']
                if kind in ('hand-accepted', 'hand-rollback', 'hand-refused') and row.get('rule') != client:
                    raise ValueError("A hand event differs from its native entry client.")
                if kind == 'feedback':
                    message = {'level': row['level'], 'message': self.events.text_field(ref, 'message')}
                    if row.get('trial') is True:
                        clause = row.get('clause')
                        if not isinstance(clause, str) or clause not in descriptor['commands'] or clause in completed:
                            raise ValueError("Trial feedback lacks exact clause attribution.")
                        feedback[clause].append(message)
                        if clause == 'liShow':
                            point['hint_log']['events'].append(dict(message, origin='discarded-hand-trial', clause=clause))
                    elif row.get('trial') is False:
                        if row['level'] == 'debug' or any(name in message['message'] for name in descriptor['log_filter']):
                            point['hint_log']['events'].append(dict(message, origin='native-invocation'))
                    else:
                        raise ValueError("Feedback lacks exact trial attribution.")
                elif kind == 'hand-accepted':
                    clause = row['clause']
                    if clause in accepted or clause in completed:
                        raise ValueError("A hand trial repeats its accepted clause.")
                    accepted[clause] = True
                elif kind == 'hand-rollback':
                    clause = row['clause']
                    if clause in completed or row.get('exact') is not True:
                        raise ValueError("A hand trial lacks unique exact rollback.")
                    completed.add(clause)
                    command = descriptor['commands'][clause]
                    base = 'invocation-%d:clause-%s:' % (number, clause)
                    trial = {'clause': clause, 'command': command,
                             'outcome': 'accepted' if accepted.pop(clause, False) else 'refused',
                             'before': 'invocation-%d:entry' % number,
                             'after_trial': base + 'after', 'rollback': base + 'rollback',
                             'rollback_equal': row['exact'], 'feedback': feedback.pop(clause, [])}
                    if trial['outcome'] == 'refused':
                        trial['after_trial_status'] = 'Failure restores the entry state. No discarded partial state is inferred.'
                    point['hand_call'].append(trial)
                elif kind == 'hand-refused':
                    if row.get('trial') is not False:
                        raise ValueError("A refusal lacks exact native attribution.")
                    if not point['hand_call'] or point['hand_call'][-1]['clause'] != row['clause']:
                        raise ValueError("A refusal lacks its exact preceding trial.")
                    trial = point['hand_call'][-1]
                    if trial['outcome'] != 'refused':
                        raise ValueError("An accepted trial cannot have a refusal record.")
                    message = self.events.text_field(ref, 'refusal')
                    if 'message' in trial:
                        raise ValueError("A refused trial repeats its refusal record.")
                    trial['message'] = message
                    point['refusal'].append({'hand_call_index': len(point['hand_call']) - 1,
                                             'clause': row['clause'], 'message': message,
                                             'exposure': 'not-exposed' if row['clause'] == 'whole-rule' else 'exposed'})
                elif kind == 'branch-counter':
                    if row.get('client') != client or row.get('trial') is not False:
                        raise ValueError("A branch result differs from its native entry identity.")
                    point['trigger']['branch_status'].append({'kind': row['outcome']})
            if accepted or feedback:
                raise ValueError("A selected invocation has an unfinished hand trial.")
            if completed != set(descriptor['commands']):
                raise ValueError("A selected invocation lacks its exact declared trial set.")
            for trial in point['hand_call']:
                if trial['outcome'] == 'refused' and 'message' not in trial:
                    raise ValueError("A refused trial lacks its exact refusal record.")
                trial['commands'] = [{'command': trial['command'], 'before': self._pointer(trial['before']),
                                      'after': self._pointer(trial['after_trial']), 'outcome': trial['outcome'],
                                      'refusal': trial.get('message')}]
            yield point
