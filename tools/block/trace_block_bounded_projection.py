"""Project checked bounded captures without treating printed text as complete terms."""
from collections import Counter
from contextlib import ExitStack, closing as _closing
import json
from pathlib import Path

from trace_block import logical_session_id
from trace_block_bounded_capture import BoundedCapture
from trace_block_bounded_points import BoundedPoints
from trace_block_bounded_prepare import bind_bounded_descriptors, bounded_guard_manifest_environment
from trace_block_bounded_session import session_operation
from trace_block_bounded_ranges import RangeIndex, partition_owned_events
from trace_block_bounded_operation import _response
from trace_block_filtered_closure import verify_kernel_closure
from trace_block_filtered_events import EventFiles, checkpoint_attribution
from trace_block_filtered import CounterProjection
from trace_block_kernel_artifacts import ArtifactReader
from trace_block_lazy_capture import LazyCapture
from trace_block_seal import file_sha256
from trace_block_stream import json_document


def relative_reference(path, root):
    path = Path(path)
    return {'path': path.relative_to(root).as_posix(), 'sha256': file_sha256(path),
            'bytes': path.stat().st_size}


def trial_plan(descriptor):
    """Require a retained ordered plan instead of reconstructing JSON object order."""
    plan = descriptor.get('trials')
    if not isinstance(plan, list) or not plan:
        raise ValueError('The bounded descriptor lacks its ordered trial plan.')
    for trial in plan:
        if (not isinstance(trial, dict) or set(trial) != {'clause', 'command', 'exposure'}
                or trial['clause'] not in descriptor['commands']
                or trial['command'] != descriptor['commands'][trial['clause']]
                or trial['exposure'] not in {'exposed', 'not-exposed'}):
            raise ValueError('A bounded trial differs from its exact command binding.')
    if set(row['clause'] for row in plan) != set(descriptor['commands']):
        raise ValueError('The bounded trial plan omits a declared command.')
    if plan[-1]['clause'] != 'whole-rule':
        raise ValueError('The automatic whole-rule trial must be the last occurrence.')
    return descriptor


class ProjectionView:
    """Keep complete referenced terms checked and operation gaps explicit.

    The caller must seal the complete raw root after normal capture closure.
    Operation maps require an independently sealed event-range record.
    """
    def __init__(self, request, evidence_dir, *, index_dir, operation_bindings=None, raw_seal_reference=None):
        self.request = request
        self.root = Path(evidence_dir).resolve(strict=True)
        self.index_dir = Path(index_dir).absolute()
        if self.index_dir.resolve().is_relative_to(self.root):
            raise ValueError('The bounded projection indexes must remain outside raw evidence.')
        self.session = json.loads((self.root / 'SESSION.json').read_text())
        self.session_reference = relative_reference(self.root / 'SESSION.json', self.root)
        self.session_id = logical_session_id(request)
        from trace_block_selected_feedback import raw_policy
        policy = raw_policy(request)
        runtime = request.get('observer_runtime', {})
        if runtime.get('surface_policy') != 'bounded-kernel-v1':
            raise ValueError('The bounded projection requires its exact surface policy.')
        self.raw_budget = None
        if policy == 'trigger-selected-raw-v2':
            from trace_block_raw_budget_validation import verify_raw_budget
            if raw_seal_reference is not None:
                self.raw_budget = verify_raw_budget(self.root.parent, self.session, raw_seal_reference)
        self._session_identity()
        descriptors = bind_bounded_descriptors(request['entry_descriptors'])
        descriptors = {client: trial_plan(value) for client, value in descriptors.items()}
        bounded_guard_manifest_environment(request['workspace'], descriptors, request['guard_manifest'])
        process = self.session['ownership']['pet']
        self.process = process
        paths = sorted((self.root / 'events' / ('process-%d' % process['pid'])).glob('event-*.json'))
        self.references = [{'path': path.relative_to(self.root).as_posix(), 'sha256': file_sha256(path)} for path in paths]
        self.events = EventFiles(self.root, self.references, process)
        self.stack = ExitStack()
        try:
            metadata = self.stack.enter_context(ArtifactReader(self.root, self.index_dir / 'metadata'))
            captures = {}
            self.rows = [(ref, self.events.read(ref)) for ref in self.references]
            for reference, event in self.rows:
                if 'capture' not in event:
                    continue
                number = event['sequence']
                prefix = 'kernel/process-%d/event-%08d/' % (process['pid'], number)
                document = self.stack.enter_context(LazyCapture(self.root, event['capture'],
                    'event-%08d/capture' % number, self.index_dir / ('capture-%08d.sqlite' % number)))
                kernel = self.session['kernel_runtime']
                captures[number] = BoundedCapture(metadata, document.root, sequence=number,
                    expected_reader=kernel['reader'], expected_toolchain_ref=kernel['toolchain_ref'],
                    expected_marker_plan=relative_reference(self.root / (prefix + 'PLAN.json'), self.root),
                    expected_arguments=[str(self.root), str(self.root / (prefix + 'PLAN.json')),
                                        kernel['toolchain_ref']['sha256'], '--result-ref'])
                captures[number].event_reference = dict(reference)
                captures[number].capture_envelope = event['capture']
                captures[number].owned_process = dict(process)
            from trace_block_rollback_reference import resolve_rollback_references
            captures = resolve_rollback_references(self.events, captures)
            self.checked_selected_feedback = None
            if policy == 'trigger-selected-raw-v2':
                self._status()
                from trace_block_selected_feedback import bind_selected_feedback
                record = self.session.get('observer_status')
                self.checked_selected_feedback = bind_selected_feedback(self.events,
                    None if record is None else record['status'])
            self.operation_bindings = operation_bindings
            operations = self._operations(captures)
            if policy != 'trigger-selected-raw-v2':
                self._status()
            self.counter_projection = CounterProjection(descriptors, self.process)
            self.counter_projection.descriptors = descriptors
            for _, row in self.native_rows:
                if row['kind'] == 'guard-counter':
                    self.counter_projection.add(row)
            self.points = BoundedPoints(self.native_events, captures, descriptors, self.session_id, operations)
            self.selected_feedback = None
            if policy == 'trigger-selected-raw-v2':
                from trace_block_selected_feedback import apply_selected_feedback
                status = self.session.get('observer_status')
                self.selected_feedback = apply_selected_feedback(self.points.points,
                    None if status is None else status['status'])
                self.selected_feedback.update(self.checked_selected_feedback)
                for point in self.points.points:
                    point['hint_log']['selected_feedback'].update(self.checked_selected_feedback)
            self._residual(captures)
            self._record_rule_successes()
            verify_kernel_closure(self.session, request, evidence_dir=self.root)
            self.header = self._header(captures)
        except BaseException:
            self.close()
            raise

    def _record_rule_successes(self):
        """Bind named-rule certificates to exact checked point occurrences."""
        from trace_block_bounded_success import rule_success
        self.rule_successes = []
        for number, point in enumerate(self.points.points):
            client = point['trigger']['client']
            descriptor = self.request['entry_descriptors'][client]
            command = descriptor['commands']['whole-rule']
            certificate = rule_success(point, self.points.snapshots, command,
                self.session_id, expected_rule=descriptor['rule'])
            if certificate is not None:
                point['rule_success'] = certificate
                self.rule_successes.append({'rule': descriptor['rule'],
                    'evidence': '#/points/%d/rule_success' % number})

    def _session_identity(self):
        operations = self.session.get('operations')
        if not isinstance(operations, list):
            raise ValueError('The bounded SESSION lacks its actual operation list.')
        starts = [row for row in operations if row.get('tool') == 'rocq_trace_start']
        expected = {key: self.request[name] for key, name in
                    [('workspace', 'workspace'), ('file', 'source'), ('theorem', 'theorem')]}
        if len(starts) != 1 or starts[0].get('arguments') != expected:
            raise ValueError('The bounded SESSION start differs from the retained request.')
        from trace_block_bounded_session import _owned
        reference, path = _owned(self.root, starts[0]['path'], starts[0]['sha256'])
        result = _response(json.loads(path.read_text()))
        if result.get('file') != expected['file'] or result.get('theorem') != expected['theorem']:
            raise ValueError('The bounded SESSION accepted another source or theorem.')
        manifest = json.loads((self.root / 'RUN-MANIFEST.json').read_text())
        if (manifest.get('revisions') != self.session.get('revisions')
                or manifest.get('prepared_instrumentation') != self.request.get('instrumentation')
                or manifest.get('kernel_runtime') != self.session.get('kernel_runtime')):
            raise ValueError('The bounded run manifest differs from its request or SESSION.')
        kernel = self.session.get('kernel_runtime')
        if not isinstance(kernel, dict) or kernel.get('surface_policy') != 'bounded-kernel-v1':
            raise ValueError('The SESSION lacks its bounded runtime binding.')
        runtime = self.request['observer_runtime']
        for field, source in [('source_reader', 'kernel_reader'), ('source_toolchain', 'kernel_toolchain')]:
            if kernel.get(field) != runtime[source]:
                raise ValueError('The SESSION changes a requested bounded runtime source.')
        from trace_block_kernel_display import artifact
        for field, source in [('reader', 'kernel_reader'), ('toolchain_ref', 'kernel_toolchain')]:
            reference = kernel[field]
            artifact(self.root, reference)
            if any(reference[key] != runtime[source][key] for key in ('sha256', 'bytes')):
                raise ValueError('The copied bounded runtime differs from its requested source.')
        loaded = self.session.get('loaded_kernel_runtime')
        if loaded is not None:
            if loaded.get('pet') != self.session['ownership']['pet']:
                raise ValueError('The loaded bounded runtime belongs to another Pet.')
            inventory = {row['path']: row for row in kernel['artifacts']}
            for row in list(loaded.get('mappings', [])) + [loaded['executable']]:
                expected = inventory.get(row['path'])
                if expected is None or any(row[key] != expected[key] for key in ('sha256', 'bytes')):
                    raise ValueError('A loaded runtime artifact lacks its exact prelaunch binding.')

    def _status(self):
        record = self.session.get('observer_status')
        if record is None:
            return
        if not isinstance(record, dict) or set(record) != {'operation', 'status'}:
            raise ValueError('The SESSION observer status schema is unsupported.')
        matches = [(index, row) for index, row in enumerate(self.session['operations'])
                   if {key: row.get(key) for key in ('path', 'sha256')} == record['operation']]
        if len(matches) != 1:
            raise ValueError('The observer status lacks its exact SESSION operation.')
        index, row = matches[0]
        from trace_block_kernel_runtime import status_command, parse_observer_status_payload
        from trace_block_bounded_operation import _response
        operation = session_operation(self.root, self.session_reference, index,
            expected_command=status_command(self.session.get('closure_check') is not None),
            expected_source_state=row['arguments']['from_state'], expected_trial=True)
        response = _response(json.loads((self.root / operation['operation']['path']).read_text()))
        from trace_block_selected_feedback import checked_status_payload
        if parse_observer_status_payload(checked_status_payload(self.root, response)) != record['status']:
            raise ValueError('The observer status differs from its accepted query response.')

    def _operations(self, captures):
        if self.operation_bindings is not None:
            raise ValueError('The projection accepts only ranges retained in the exact SESSION.')
        recorded = any('event_range' in row for row in self.session['operations'])
        self.range_index = None
        self.native_rows = self.rows
        self.discarded_references = []
        self.operation_gaps = []
        if not recorded:
            self.native_events = self.events
            self.operation_gaps = [reference['path'] for reference, _ in self.rows]
            return {number: {'availability': 'unavailable',
                'reason': 'The capture backend records no event range for each operation.'}
                    for number in captures}
        self.range_index = self.stack.enter_context(_closing(RangeIndex(self.root, self.session,
            index_dir=self.index_dir / 'operation-ranges')))
        def validate(index):
            operation = self.session['operations'][index]
            if operation['tool'] != 'rocq_trace_run':
                raise ValueError('An observed proof event belongs to a non-tactic operation.')
            response = _response(json.loads(Path(operation['path']).read_text()))
            return session_operation(self.root, self.session_reference, index,
                expected_command=operation['arguments']['command'],
                expected_source_state=operation['arguments']['from_state'],
                expected_trial=operation['arguments']['trial'], expected_accepted=response['accepted'])
        partition = partition_owned_events(self.events, self.range_index, self.process, validate)
        self.discarded_references = partition['sdk_discarded_references']
        self.operation_gaps = [ref['path'] for ref in partition['missing_references']]
        self.native_events = EventFiles(self.root, partition['native_references'], self.process)
        self.native_rows = [(ref, self.events.read(ref)) for ref in partition['native_references']]
        bindings = {}
        for reference, row in self.native_rows:
            number = row['sequence']
            if number not in captures:
                continue
            operation = partition['operations'].get(reference['path'])
            if operation is None:
                bindings[number] = {'availability': 'unavailable',
                    'reason': 'The SESSION ranges do not bind this capture event.'}
                continue
            index = operation['operation_index']
            bindings[number] = {'availability': 'complete',
                'session_operation': 'evidence/SESSION.json#/operations/%d' % index,
                'event_range': 'evidence/SESSION.json#/operations/%d/event_range' % index,
                'trial': operation['trial'], 'accepted': operation['accepted'],
                'retention_method': operation['retention_method']}
        return bindings

    def _residual(self, captures):
        reference = self.session.get('residual_event')
        found = [(ref, row) for ref, row in self.native_rows if row['kind'] == 'checkpoint'
                 and row.get('rule') == 'residual' and row.get('trial') is False]
        if reference is None:
            if found:
                raise ValueError('The owned stream contains an unassociated full residual.')
            return
        matches = [(ref, row) for ref, row in found
                   if reference == {'path': str(self.root / ref['path']), 'sha256': ref['sha256']}]
        if len(matches) != 1 or len(found) != 1:
            raise ValueError('The session does not bind its exact first residual.')
        number = matches[0][1]['sequence']
        if number not in captures:
            raise ValueError('The first residual lacks its checked complete capture.')
        if captures[number].proof['availability'] != 'bounded-display':
            raise ValueError('The first residual lacks its checked partial proof display.')
        selection = self.session.get('residual_selection')
        expected_fields = {'scope', 'command', 'event', 'selector', 'selected_goal_id',
            'captured_current_goals', 'shelf_count', 'given_up_count', 'hidden_peer_goals'}
        if not isinstance(selection, dict) or set(selection) != expected_fields:
            raise ValueError('The bounded residual lacks its exact leaf selection record.')
        for field in ('selected_goal_id', 'captured_current_goals', 'shelf_count', 'given_up_count'):
            if type(selection[field]) is not int or selection[field] < 0:
                raise ValueError('A bounded residual selection count or identity is invalid.')
        if type(selection.get('selector', {}).get('value')) is not int:
            raise ValueError('The bounded residual selector is not an exact integer.')
        capture = captures[number]
        goals = capture.groups['goals']
        if (selection['scope'] != 'first-focused-leaf'
                or selection['selector'] != {'kind': 'focused-index', 'value': 1}
                or selection['event'] != reference
                or selection['command'] != '1: ltac2:(trace_bounded_snapshot "residual").'
                or len(goals) != 1 or selection['selected_goal_id'] != goals[0]['id']
                or selection['captured_current_goals'] != len(goals)
                or selection['shelf_count'] != len(capture.groups['shelf'])
                or selection['given_up_count'] != len(capture.groups['given_up'])):
            raise ValueError('The bounded residual selection differs from its actual captured leaf.')
        if selection['hidden_peer_goals'] != {'availability': 'unavailable',
                'reason': 'This selected Proofview capture does not expose hidden focus frames.'}:
            raise ValueError('The residual must keep hidden peer goals explicitly unavailable.')
        self.points.residual['selection'] = {key: selection[key] for key in
            ('scope', 'selector', 'selected_goal_id', 'hidden_peer_goals')}
        self.points.residual['selection']['evidence'] = 'evidence/SESSION.json#/residual_selection'

        if self.session.get('residual_trials'):
            raise ValueError('Bounded residual SDK trials require a separate exact range adapter.')

    def _header(self, captures):
        reasons = []
        from trace_block_selected_feedback import raw_policy
        if raw_policy(self.request) == 'trigger-selected-raw-v2':
            feedback = getattr(self, 'selected_feedback', None)
            if not isinstance(feedback, dict) or feedback.get('availability') != 'complete':
                reasons.append('The selected feedback is unavailable or incomplete.')
            budget = getattr(self, 'raw_budget', None)
            if not isinstance(budget, dict) or budget.get('complete') is not True:
                reasons.append('The final raw budget lacks complete sealed validation.')
        counters = [(ref, row) for ref, row in self.native_rows if row['kind'] == 'guard-counter']
        rules = sorted({value['rule'] for value in self.request['entry_descriptors'].values()})
        attempted = {rule: 0 for rule in rules}
        actual = dict(attempted)
        unknown = dict(attempted)
        for _, row in counters:
            decision = row.get('classification')
            if decision not in {'actual-trigger', 'non-trigger', 'unknown'}:
                raise ValueError('The native guard classification is unsupported.')
            attempted[row['rule']] += 1
            actual[row['rule']] += decision == 'actual-trigger'
            unknown[row['rule']] += decision == 'unknown'
        point_counts = Counter(point['trigger']['rule'] for point in self.points.points)
        if hasattr(self, 'counter_projection'):
            checked = self.counter_projection.coverage([{'process': self.process,
                'client': point['trigger']['client'], 'invocation': point['trigger']['invocation']}
                for point in self.points.points])
            attempted, actual, unknown = (checked[key] for key in ('attempted_entries', 'actual_triggers', 'unknown_guards'))
        if any(point_counts[rule] != actual[rule] for rule in rules):
            reasons.append('A typed trigger lacks its exact selected capture.')
        if any(unknown.values()):
            reasons.append('A native typed guard has an unknown result.')
        checkpoints = []
        for reference, row in self.native_rows:
            if row['kind'] == 'checkpoint-counter' and row.get('trial') is False:
                state, complete = checkpoint_attribution(row)
                checkpoints.append({'reference': reference, 'record': row, 'state': state, 'complete': complete})
        self.checkpoints = checkpoints
        lookups = [row for row in checkpoints if row['record']['label'] == 'instruction-lookup']
        provenance = bool(lookups) and all(row['complete'] for row in lookups)
        if not provenance:
            reasons.append('The native instruction provenance is unavailable or incomplete.')
        for field in ('entry_coverage_complete', 'instruction_coverage_complete'):
            if self.request.get('instrumentation', {}).get(field) is not True:
                reasons.append('The preparation lacks complete instrumentation: ' + field)
        if self.operation_gaps:
            reasons.append('The owned stream lacks exact recorded operation ranges for some events.')
        if self.range_index is not None and self.range_index.incomplete:
            reasons.append('Some recorded operation ranges are incomplete.')
        owner = self.session.get('ownership', {})
        for key in ('transport_closed_normally', 'owned_pet_exited'):
            if owner.get(key) is not True:
                reasons.append('The session lacks normal owned closure: ' + key)
        if self.session.get('source_unchanged') is not True:
            reasons.append('The session does not establish unchanged source inputs.')
        if self.session.get('error') is not None:
            reasons.append('The owned capture session reports an error.')
        if self.session.get('observation_complete') is not True:
            reasons.append('The backend does not establish complete observation.')
        status = self.session.get('observer_status')
        if (not isinstance(status, dict) or not isinstance(status.get('status'), dict)
                or status['status'].get('complete') is not True):
            reasons.append('The bounded observer status is missing or incomplete.')
        closed = self.session.get('closure_check') is not None
        if closed == (self.points.residual is not None):
            reasons.append('The capture lacks one terminal outcome: accepted Qed or first residual.')
        stop = self.request['stop']
        if stop['kind'] == 'rule':
            occurred = actual.get(stop['value'], 0) > 0
        elif stop['kind'] == 'residual':
            occurred = self.points.residual is not None
        else:
            occurred = any(row['record']['label'] == 'requested-trigger' for row in checkpoints)
        verdict = {'status': 'unresolved', 'kind': None, 'session': self.session_id,
                   'reason': 'Terminal rule evidence or complete proof closure is unavailable.'}
        if not reasons and getattr(self, 'rule_successes', []):
            success = self.rule_successes[0]
            verdict = {'status': 'actual-success', 'kind': 'rule_success', 'session': self.session_id,
                       'rule': success['rule'], 'evidence': success['evidence']}
        elif not reasons and closed:
            verdict = {'status': 'actual-success', 'kind': 'proof_closure', 'session': self.session_id,
                       'evidence': 'evidence/SESSION.json#/closure_check'}
        return {'schema_version': 1, 'surface_policy': 'bounded-kernel-v1',
            'request': {key: self.request[key] for key in ('block_pc', 'rule_set', 'stop', 'scope')},
            'identity': dict(self.request['scope']),
            'session': {'id': self.session_id, 'runtime': 'evidence/SESSION.json'},
            'pet_start_tick': 'evidence/SESSION.json#/ownership/pet/start_ticks',
            'runtime_evidence': 'evidence/SESSION.json',
            'coverage': {'attempted_entries': attempted, 'actual_triggers': actual,
                'captured_events': {rule: point_counts[rule] for rule in rules}, 'unknown_guards': unknown,
                'instruction_provenance_complete': provenance, 'required_complete': not reasons,
                'requested_trigger': 'occurred' if occurred else 'unobserved' if reasons else 'not-occurred',
                'raw_event_index': 'raw/INDEX.json', 'unobserved_regions': list(reasons)},
            'completion': {'trace_complete': not reasons, 'proof_closed': closed,
                'closure_check': self.session.get('closure_check'), 'reasons': reasons},
            'verdict': verdict}

    @property
    def trace(self):
        return dict(self.header, points=self.points.points, snapshots=self.points.snapshots,
                    residual=self.points.residual, instruction_visits=[])

    def write_raw_index(self, path):
        record = {'schema': 1, 'surface_policy': 'bounded-kernel-v1', 'session': self.session_id,
            'process': self.process, 'guard_manifest': self.request['guard_manifest'],
            'events': self.references,
            'guard_counters': [{'reference': ref, 'record': row} for ref, row in self.rows if row['kind'] == 'guard-counter'],
            'checkpoints': self.checkpoints,
            'capture_sequences': sorted(int(key.removeprefix('event-')) for key in self.points.snapshots),
            'sdk_discarded_events': self.discarded_references, 'operation_gaps': self.operation_gaps,
            'operation_events': None if self.range_index is None else self.range_index.by_event}
        with Path(path).open('x') as stream:
            for part in json_document(record):
                stream.write(part)

    def close(self):
        self.stack.close()

    def __enter__(self):
        return self

    def __exit__(self, *arguments):
        self.close()
