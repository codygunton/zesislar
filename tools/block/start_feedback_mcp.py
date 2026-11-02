"""Retain PET start diagnostics without changing the selected position or command."""
import inspect


SEVERITIES = {1: 'error', 2: 'warning', 3: 'information', 4: 'hint'}
START_PARAMETERS = ('file', 'theorem', 'workspace', 'lifespan_state', 'line',
                    'character', 'preamble', 'force_restart', 'timeout')


def retain_feedback(result, entry):
    """Use the returned State schema. Empty printed goals grant no success."""
    value = dict(result)
    if result.get('success') is not True:
        value['start_feedback'] = {'available': False, 'reason': 'start_failed'}
        return value
    if entry is None:
        raise ValueError('The successful start lacks its returned PET state.')
    state = entry.state
    if type(state.proof_finished) is not bool or not isinstance(state.feedback, list):
        raise ValueError('The returned PET state has an unsupported schema.')
    feedback = []
    for row in state.feedback:
        if (not isinstance(row, (list, tuple)) or len(row) != 2
                or type(row[0]) is not int or row[0] not in SEVERITIES
                or not isinstance(row[1], str)):
            raise ValueError('The returned PET feedback has an unsupported schema.')
        feedback.append({'severity': row[0], 'kind': SEVERITIES[row[0]],
                         'message': row[1]})
    if result.get('proof_finished') != state.proof_finished:
        raise ValueError('The returned start and PET state disagree.')
    value['start_feedback'] = {'available': True,
                              'schema': 'pytanque.State.feedback.lsp.v1',
                              'messages': feedback}
    errors = [row for row in feedback if row['severity'] == 1]
    if errors:
        value.update(success=False, reason='document_error',
                     error='PET reported an error while processing the start document.')
    return value


def install_start_feedback(server, interactive):
    """Wrap this SDK entrypoint in memory. Preserve its public tool signature."""
    original = server.run_start
    if getattr(original, '_retains_start_feedback', False):
        return
    signature = inspect.signature(original)
    if (tuple(signature.parameters) != START_PARAMETERS
            or not callable(getattr(interactive, '_state_get', None))):
        raise ValueError('The installed start handler has an unsupported interface.')

    async def start(*args, **kwargs):
        arguments = signature.bind(*args, **kwargs)
        arguments.apply_defaults()
        result = await original(*args, **kwargs)
        if result.get('success') is not True:
            return retain_feedback(result, None)
        state_id = result.get('state_id')
        if type(state_id) is not int:
            return dict(result, success=False, reason='start_feedback_unavailable',
                        error='The successful start lacks its returned state ID.')

        def capture(pet):
            try:
                return retain_feedback(result, interactive._state_get(state_id))
            except (AttributeError, ValueError) as error:
                return dict(result, success=False, reason='start_feedback_unavailable',
                            error=str(error))

        captured = await server._run_with_pet(capture, arguments.arguments['lifespan_state'],
                                              'rocq_start', timeout=arguments.arguments['timeout'])
        if 'start_feedback' not in captured:
            captured = dict(result, **captured)
            captured['start_feedback'] = {'available': False, 'reason': 'capture_failed'}
        return captured

    start._retains_start_feedback = True
    server.run_start = start
