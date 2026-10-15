"""Join SDK-discarded residual trials to their exact full captures."""

import hashlib
import json
from pathlib import Path

from trace_block_seal import checked_reference
from trace_block_filtered_closure import _owned

CHECKPOINT = 'all: ltac2:(trace_block_snapshot "residual").'


class ResidualTrials:
    """Retain whole before states and identify the selected residual leaf."""

    def __init__(self, request, session, points, residual_reference):
        self.points = points
        self.root = points.events.root
        self.records = []
        self.event_paths = set()
        self.selected_goal = None
        supplied = session.get('residual_trials', [])
        declared = request.get('residual_trials', [])
        if not isinstance(supplied, list) or not isinstance(declared, list) or len(supplied) != len(declared):
            raise ValueError('The SESSION lacks its exact declared residual trial set.')
        if not supplied:
            return
        if residual_reference is None or session.get('closure_check') is not None:
            raise ValueError('Residual trials require the original open residual.')
        selection = session.get('residual_selection', {})
        if (selection.get('scope') != 'first-focused-leaf'
                or selection.get('selector') != {'kind': 'focused-index', 'value': 1}
                or type(selection.get('selected_goal_id')) is not int
                or selection['selected_goal_id'] <= 0):
            raise ValueError('Residual trials lack the exact selected leaf identity.')
        expected_event = dict(residual_reference, path=str(points.events.root/residual_reference['path']))
        if selection.get('event') != expected_event or selection.get('captured_current_goals') != 1:
            raise ValueError('The selected residual metadata has a different owned event.')
        self.selected_goal = selection['selected_goal_id']
        initial = points._capture(residual_reference)
        if not initial['current_goals'] or initial['current_goals'][0]['id'] != self.selected_goal:
            raise ValueError('The selected trial leaf differs from the first residual.')
        operations = session['operations']
        used_operations = set()
        last_sequence = points.events.read(residual_reference)['sequence']
        for index, (expected, actual) in enumerate(zip(declared, supplied)):
            for field in ('name', 'rule', 'command', 'command_sha256', 'sources'):
                if actual.get(field) != expected.get(field):
                    raise ValueError('A residual trial differs from its frozen request: ' + field)
            command = actual['command']
            if (actual['rule'] != 'FinishFacts' or not isinstance(command, str)
                    or hashlib.sha256(command.encode()).hexdigest() != actual['command_sha256']
                    or actual.get('execution') != 'SDK-discarded' or actual.get('native_entry') is not False
                    or actual.get('refusal_exposure') != expected.get('exposure')
                    or expected.get('exposure') not in ('exposed', 'not-exposed')):
                raise ValueError('A residual trial lacks its exact rule and command binding.')
            for source in actual['sources']:
                checked_reference(source)
            executed = command + ' ' + CHECKPOINT
            if actual.get('executed_command') != executed:
                raise ValueError('The discarded residual command differs from its declared command.')
            matches = [i for i, operation in enumerate(operations)
                       if operation.get('tool') == 'rocq_trace_run'
                       and operation.get('arguments', {}).get('command') == executed]
            if len(matches) != 1 or matches[0] in used_operations or not 0 < matches[0] < len(operations) - 1:
                raise ValueError('A residual trial lacks its unique same-session operation.')
            number = matches[0]
            used_operations.add(number)
            previous, operation, following = operations[number - 1:number + 2]
            before_response = self._operation(previous, CHECKPOINT, False)
            trial_response = self._operation(operation, executed, True)
            rollback_response = self._operation(following, CHECKPOINT, False)
            if (trial_response != actual['result'] or before_response.get('accepted') is not True
                    or rollback_response.get('accepted') is not True
                    or before_response.get('state_id') != actual.get('before_state_id')
                    or operation['arguments'].get('from_state') != actual['before_state_id']
                    or trial_response.get('state_id') != actual['before_state_id']
                    or following['arguments'].get('from_state') != actual['before_state_id']):
                raise ValueError('A residual trial has a different persistent source state.')
            response = self._record(trial_response)
            state_check = response.get('retained_state_check', {})
            if (response.get('retained_state_hash_unchanged') is not True
                    or state_check.get('method') != 'Pet.state_hash'
                    or type(state_check.get('before')) is not int
                    or state_check['before'] != state_check.get('after')
                    or state_check != actual.get('state_check')):
                raise ValueError('A discarded residual trial lacks public state-hash equality.')
            accepted = trial_response.get('accepted')
            if type(accepted) is not bool or response.get('accepted') != accepted:
                raise ValueError('A residual trial has an inconsistent accepted response.')
            keys = {}
            for role in ('before', 'after', 'rollback'):
                references = actual.get(role)
                required = role != 'after' or accepted
                if not isinstance(references, list) or len(references) != (1 if required else 0):
                    raise ValueError('A residual trial lacks its exact full ' + role + ' capture.')
                if not required:
                    if actual.get('after_availability') != 'not-retained':
                        raise ValueError('A refused trial claims a discarded partial state.')
                    continue
                reference = self._event(references[0])
                row = points.events.read(reference)
                if row['sequence'] <= last_sequence:
                    raise ValueError('Residual trial captures repeat or change their exact operation order.')
                last_sequence = row['sequence']
                key = 'residual-trial-%d:%s' % (index, role)
                points.snapshot_rows[key] = reference
                keys[role] = key
            before = points.get_snapshot(keys['before'])
            rollback = points.get_snapshot(keys['rollback'])
            before_ref = points.snapshot_rows[keys['before']]
            rollback_ref = points.snapshot_rows[keys['rollback']]
            if (before != rollback or points.documents[before_ref['path']].root
                    != points.documents[rollback_ref['path']].root):
                raise ValueError('A residual trial has different full before and rollback captures.')
            if not before['current_goals'] or before['current_goals'][0]['id'] != self.selected_goal:
                raise ValueError('A residual trial changed the selected leaf identity.')
            if any(initial[field] != before[field] for field in ('goal', 'goal_nonotation', 'hyps', 'shelf', 'given_up', 'evars')):
                raise ValueError('A residual trial does not start at the original selected leaf.')
            if accepted and actual.get('after_availability') != 'captured':
                raise ValueError('An accepted residual trial lacks its discarded after capture.')
            if not accepted:
                keys['after'] = keys['rollback']
            self.records.append((actual, response, keys))

    def _record(self, reference):
        return json.loads(_owned({key: reference[key] for key in ('path', 'sha256')}, self.root).read_text())

    def _operation(self, operation, command, trial):
        arguments = operation.get('arguments', {})
        if (operation.get('tool') != 'rocq_trace_run' or arguments.get('command') != command
                or arguments.get('trial') is not trial or arguments.get('capture_mode') != 'bounded'):
            raise ValueError('A residual trial has a different operation boundary.')
        envelope = self._record(operation)
        response = envelope.get('structuredContent')
        if envelope.get('isError') is True or not isinstance(response, dict) or response.get('success') is not True:
            raise ValueError('A residual operation lacks its accepted transport response.')
        self._record(response)
        return response

    def _event(self, reference):
        checked_reference(reference)
        path = Path(reference['path'])
        relative = path.relative_to(self.points.events.root).as_posix()
        value = {'path': relative, 'sha256': reference['sha256']}
        if value not in self.points.events.references or relative in self.event_paths:
            raise ValueError('A residual trial has an extra or repeated owned event.')
        event = self.points.events.read(value)
        if event.get('kind') != 'checkpoint' or event.get('rule') != 'residual' or event.get('trial') is not False:
            raise ValueError('A residual trial does not reference the supported full checkpoint.')
        self.event_paths.add(relative)
        return value

    def decorate(self, residual):
        """Attach truthful discarded trials without claiming a native rule entry."""
        for actual, response, keys in self.records:
            accepted = actual['result']['accepted']
            message = None if accepted else response.get('message')
            if not accepted and (not isinstance(message, str) or not message):
                raise ValueError('A refused residual trial lacks its exact message.')
            trial = {'clause': actual['name'], 'rule': actual['rule'], 'scope': 'residual-leaf',
                     'selected_goal_id': self.selected_goal, 'execution': 'SDK-discarded', 'native_entry': False,
                     'command': actual['command'], 'outcome': 'accepted' if accepted else 'refused',
                     'before': keys['before'], 'after_trial': keys['after'], 'rollback': keys['rollback'],
                     'rollback_equal': True, 'feedback': [],
                     'state_hash_check': actual['state_check'],
                     'commands': [{'command': actual['command'], 'before': self.points._pointer(keys['before']),
                                   'after': self.points._pointer(keys['after']),
                                   'outcome': 'accepted' if accepted else 'refused', 'refusal': message}]}
            if not accepted:
                trial.update(message=message, after_trial_status='Failure restores the retained state. The discarded partial state is unavailable.')
                residual['refusal'].append({'hand_call_index': len(residual['hand_call']),
                    'clause': actual['name'], 'message': message, 'exposure': actual['refusal_exposure']})
            residual['hand_call'].append(trial)
        return residual
