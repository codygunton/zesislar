"""Project a closed filtered SESSION with bounded schema2 payload readers."""

import json
from pathlib import Path

from trace_block import logical_session_id
from trace_block_filtered_closure import verify_kernel_closure
from trace_block_filtered_events import FilteredEvents
from trace_block_filtered_points import FilteredPoints
from trace_block_residual_trials import ResidualTrials
from trace_block_filtered_seal import filtered_index_rows
from trace_block_seal import checked_reference, file_sha256
from trace_block_stream import json_document


class ProjectionView:
    """Keep logical captures lazy until both generated outputs are sealed."""

    def __init__(self, request, evidence_dir, *, index_dir):
        self.request = request
        self.directory = Path(evidence_dir).resolve(strict=True)
        if Path(index_dir).resolve().is_relative_to(self.directory):
            raise ValueError('Projection indexes must remain outside the immutable evidence root.')
        self.session_path = self.directory/'SESSION.json'
        self.session = json.loads(self.session_path.read_text())
        if not isinstance(request.get('observer_runtime'), dict):
            raise ValueError('The schema2 projection requires the bound filtered runtime.')
        verify_kernel_closure(self.session, request, evidence_dir=self.directory)
        self.session_id = logical_session_id(request)
        process = self.session['ownership']['pet']
        if process is None:
            raise ValueError('The filtered session has no owned Pet identity.')
        paths = sorted((self.directory/'events'/('process-%d' % process['pid'])).glob('event-*.json'))
        self.references = [{'path': path.relative_to(self.directory).as_posix(), 'sha256': file_sha256(path)}
                           for path in paths]
        self.events = FilteredEvents(self.directory, self.references, process, request['entry_descriptors'])
        self.points = FilteredPoints(self.events, request['entry_descriptors'], self.session_id, index_dir)
        try:
            self.residual_reference = None
            residuals = [(reference, self.events.read(reference)) for reference in self.references
                         if self.events.read(reference)['kind'] == 'checkpoint'
                         and self.events.read(reference).get('rule') == 'residual'
                         and self.events.read(reference).get('trial') is False]
            declared = self.session.get('residual_event')
            if declared is not None:
                matches = [(reference, row) for reference, row in residuals
                           if declared == dict(reference, path=str(self.directory/reference['path']))]
                if len(matches) != 1:
                    raise ValueError('The SESSION does not bind its exact first residual event.')
                checked_reference(declared)
                self.residual_reference = matches[0][0]
            elif residuals:
                raise ValueError('The SESSION residual reference has no matching owned event.')
            self.residual_trials = ResidualTrials(request, self.session, self.points, self.residual_reference)
            retained = {reference['path'] for reference, row in residuals}
            expected = self.residual_trials.event_paths | ({self.residual_reference['path']} if self.residual_reference else set())
            if retained != expected:
                raise ValueError('The session has an unassociated full residual checkpoint.')
            self.header = self._header()
        except BaseException:
            self.points.close()
            raise

    def close(self):
        self.points.close()

    def __enter__(self):
        return self

    def __exit__(self, *arguments):
        self.close()

    @property
    def snapshot_keys(self):
        return self.points.snapshot_keys + (('residual',) if self.residual_reference else ())

    def get_snapshot(self, key):
        if key == 'residual' and self.residual_reference:
            return self.points._capture(self.residual_reference)
        return self.points.get_snapshot(key)

    def iter_points(self):
        for ordinal, point in enumerate(self.points.iter_points()):
            point['trigger']['ordinal'] = ordinal
            yield point

    def iter_instruction_visits(self):
        return iter(())

    @property
    def residual(self):
        if not self.residual_reference:
            return None
        value = self.get_snapshot('residual')
        reference = self.residual_reference
        document = self.points.documents[reference['path']].root
        proof = document['show_proof']
        if proof['availability'] != 'complete' or proof['command'] != 'Show Proof.':
            raise ValueError('The filtered residual lacks complete Show Proof.')
        value.update(session_id=self.session_id, trigger={'kind': 'residual'}, hand_call=[], refusal=[],
                     hint_log={'availability': 'complete', 'filter': ['bounded residual'], 'events': []},
                     show_proof={'availability': 'complete', 'command': proof['command'],
                                 'text': proof['notation'], 'text_nonotation': proof['no_notation']})
        return self.residual_trials.decorate(value)

    def _header(self):
        request, session = self.request, self.session
        owner, closure = session['ownership'], session['closure_check']
        reasons = []
        coverage = dict(self.events.coverage)
        if not coverage['required_complete']:
            reasons.append('The filtered counter or instruction coverage is incomplete.')
        if session['error'] is not None:
            reasons.append('The owned session failed. See the complete runtime evidence.')
        if session['source_unchanged'] is not True:
            reasons.append('The prepared source changed during the session.')
        if owner.get('transport_closed_normally') is not True or owner.get('owned_pet_exited') is not True:
            reasons.append('The owned session did not close normally.')
        for field in ('entry_coverage_complete', 'instruction_coverage_complete'):
            if request.get('instrumentation', {}).get(field) is not True:
                reasons.append('The preparation lacks complete instrumentation: ' + field)
        if closure is None and self.residual_reference is None:
            reasons.append('The session has neither accepted Qed nor its first residual.')
        if closure is not None and self.residual_reference is not None:
            reasons.append('The session claims both accepted Qed and an open residual.')
        stop = request['stop']
        if stop['kind'] == 'residual':
            occurred = self.residual_reference is not None
        elif stop['kind'] == 'rule':
            occurred = coverage['actual_triggers'].get(stop['value'], 0) > 0
        else:
            occurred = any(row['label'] == 'requested-trigger' for row in self.events.checkpoints)
            if not occurred:
                occurred = any(row['kind'] == 'hand-accepted' and row.get('clause') == 'requested-trigger'
                               for row in (self.events.read(ref) for ref in self.references))
        obligations = {'availability': 'unavailable', 'session': self.session_id,
                       'counts': None, 'undefined_evars': None,
                       'evidence': 'evidence/SESSION.json#/residual_event'}
        if closure is not None:
            record = session.get('final_obligations', {})
            counts = record.get('counts')
            if (record.get('availability') != 'complete' or record.get('method') != 'kernel-accepted-Qed'
                    or not isinstance(counts, dict) or set(counts) != {'goals', 'stack', 'shelf', 'given_up'}
                    or any(type(value) is not int or value != 0 for value in counts.values())
                    or type(record.get('undefined_evars')) is not int or record['undefined_evars'] != 0
                    or record.get('evidence') != closure.get('operation')):
                raise ValueError('The accepted Qed lacks its exact empty final-obligation record.')
            checked_reference(record['evidence'])
            obligations.update(availability='complete', counts=counts, undefined_evars=0,
                               method='kernel-accepted-Qed', evidence='evidence/SESSION.json#/final_obligations')
        elif self.residual_reference is not None:
            state = self.get_snapshot('residual')
            obligations.update(counts={'goals': len(state['current_goals']), 'stack': None,
                                      'shelf': len(state['shelf']), 'given_up': len(state['given_up'])},
                               undefined_evars=sum(row['status'] == 'undefined' for row in state['evars']['entries']))
        coverage.update(required_complete=not reasons, missing_event_ids=[], unobserved_regions=list(reasons),
                        requested_trigger='occurred' if occurred else 'not-occurred',
                        requested_trigger_instruction_list=[], raw_event_index='raw/INDEX.json',
                        traversal='proof-closed' if closure is not None else 'first-residual')
        return {'identity': {**request['scope'], 'switches': {'requested': request['rule_set'],
                            'actual_instances': session['actual_switches']}, 'instrumentation': request['instrumentation']},
                'session': {'id': self.session_id, 'runtime': 'evidence/SESSION.json#/ownership/pet'},
                'pet_start_tick': 'evidence/SESSION.json#/ownership/pet/start_ticks',
                'verdict': {'status': 'unresolved', 'kind': None, 'session': self.session_id},
                'coverage': coverage, 'instruction_visits': [],
                'completion': {'trace_complete': not reasons, 'proof_closed': closure is not None,
                               'reasons': reasons, 'closure_check': closure, 'final_obligations': obligations},
                'evidence': {'path': str(self.session_path), 'sha256': file_sha256(self.session_path)},
                'owned_closure': owner}

    def write_raw_index(self, path):
        attempted, captures = filtered_index_rows(self.events)
        record = {'schema': 2, 'selection_policy': 'source-filtered-v1', 'session': self.session_id,
                  'guard_manifest': self.request['guard_manifest'], 'events': self.references,
                  'attempted_entries': attempted, 'captured_entries': captures,
                  'instruction_lookups': [row['reference'] for row in self.events.checkpoints if row['label'] == 'instruction-lookup'],
                  'requested_checkpoints': [row['reference'] for row in self.events.checkpoints if row['label'] == 'requested-trigger']}
        with Path(path).open('x', encoding='utf-8') as stream:
            for part in json_document(record):
                stream.write(part)
        return {'path': str(path), 'sha256': file_sha256(path)}
