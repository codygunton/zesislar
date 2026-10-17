"""Check instruction lookup through a separate resource-only diagnostic."""
import argparse
import asyncio
import json
from pathlib import Path
import re
import time

from call_journal import ToolJournal
import launch_entries as entries


RESOURCE_FIELDS = {'pc', 'selected_code', 'index_module', 'index_source'}


def instruction_entry(source, module, pc):
    """Read one unique pair from the pinned generated instruction map."""
    if entries.NAME.fullmatch(module) is None or not module.endswith('.instr_map'):
        raise ValueError('The resource probe needs an exact instruction-map name.')
    # Generated indexes use flat instruction comments. Reject other comment forms.
    if re.search(r'\(\*(?:(?!\*\)).)*\(\*', source, re.S):
        raise ValueError('The instruction map contains nested comments.')
    clean = re.sub(r'\(\*.*?\*\)', '', source, flags=re.S)
    maps = re.findall(r'\bDefinition\s+instr_map\s*:=\s*\[(.*?)\]\s*\.', clean, re.S)
    if len(maps) != 1:
        raise ValueError('The resource probe needs one generated instruction map.')
    pairs = []
    for row in maps[0].split(';'):
        if not row.strip():
            continue
        match = re.fullmatch(r'\s*\(\s*(0x[0-9a-fA-F]+|[0-9]+)%Z\s*,\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)\s*', row)
        if match is None:
            raise ValueError('The instruction map has an unsupported pair.')
        address = int(match[1], 16 if match[1].startswith('0x') else 10)
        pairs.append((address, match[2]))
    if len({address for address, _ in pairs}) != len(pairs):
        raise ValueError('The instruction map contains duplicate PCs.')
    found = [name for address, name in pairs if address == pc]
    if len(found) != 1:
        raise ValueError('The instruction map omits the entry PC.')
    symbol = found[0]
    modules = re.findall(r'(?m)^Require Export ([A-Za-z_][A-Za-z0-9_.]*)\s*\.', clean)
    exports = [name for name in modules if name.rsplit('.', 1)[-1] == symbol]
    if len(exports) != 1:
        raise ValueError('The instruction map needs one exact trace export.')
    return exports[0] + '.' + symbol


def make_plan(entry, resource, workspace, function):
    """Generate fixed resource commands without changing the primary source."""
    if not isinstance(resource, dict) or set(resource) != RESOURCE_FIELDS:
        raise ValueError('The resource probe has invalid fields.')
    pc_text, code, index = (resource[key] for key in ('pc', 'selected_code', 'index_module'))
    if (not isinstance(pc_text, str) or re.fullmatch(r'0x[0-9a-fA-F]+', pc_text) is None
            or not isinstance(code, str) or entries.NAME.fullmatch(code) is None
            or not isinstance(index, str) or entries.NAME.fullmatch(index) is None):
        raise ValueError('The resource probe needs exact names and a literal PC.')
    pc = int(pc_text, 16)
    if not 0 <= pc < 2 ** 64:
        raise ValueError('The entry PC is outside the architecture range.')
    checked = entries.prepare_entries([entry], workspace, function)[0]
    source = Path(checked['source']['resolved']).read_text()
    header = source.split('\nProof.\n')[0]
    marker = re.compile(r'(?m)^(?:Lemma|Theorem) ' + re.escape(entry['theorem']) + r'\b')
    start = list(marker.finditer(header))[0].start()
    declaration = header[start:]
    addresses = re.findall(r'\binstr_body\s+(0x[0-9a-fA-F]+|[0-9]+)\b', declaration)
    if len(addresses) != 1 or int(addresses[0], 16 if addresses[0].startswith('0x') else 10) != pc:
        raise ValueError('The resource PC differs from the primary declaration.')
    # A bare resource premise cannot contain parameters or an arbitrary tactic.
    bare = re.findall(r'(?m)^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*-∗\s*$', declaration)
    if bare != [code]:
        raise ValueError('The selected-code premise is absent or ambiguous.')
    index_source = entries.checked_file(resource['index_source'], Path(workspace).resolve())
    index_module = index.removesuffix('.instr_map')
    if index_module not in checked['artifacts']:
        raise ValueError('The instruction-map object lacks an exact import binding.')
    relative = Path(index_source['resolved']).relative_to(Path(workspace).resolve())
    if relative.suffix != '.v':
        raise ValueError('The instruction map source must be a Rocq file.')
    expected = instruction_entry(Path(index_source['resolved']).read_text(), index, pc)
    literal = str(pc) + '%Z'
    some = '(Some ' + expected + ')'
    goal = ('find_in_context (FindInstrKind ' + literal + ' false) '
            '(fun kind => match kind with | IKInstr instruction => '
            '⌜instruction = ' + some + '⌝ | IKPre _ _ => False end)')
    theorem = 'ResourceLookup_' + entry['id'].replace('-', '_')
    if entries.NAME.fullmatch(theorem) is None:
        raise ValueError('The resource probe has an invalid theorem name.')
    probe = (header[:start] + 'Lemma ' + theorem + ' `{!islaG Sigma} `{!threadG} :\n  ' +
             code + ' -∗\n  ' + goal + '.\nProof.\nAbort.\n')
    commands = [
        ('environment', 'iStartProof.'),
        ('map-entry', 'let checked := constr:(eq_refl : List.filter '
         '(fun item : Z * isla_trace => Z.eqb (fst item) ' + literal + ') ' + index +
         ' = cons (' + literal + ', ' + expected + ') nil) in idtac.'),
        ('registration', 'let registered := constr:(_ : LithiumUnfold (@' + code + ')) in assert_fails (has_evar registered); idtac "RESOURCE-REGISTRATION" registered.'),
        ('opening', 'lazymatch goal with | |- envs_entails _ (' + code +
         ' -∗ _) => liUnfoldEarly | _ => fail 100 "Resource preflight: unexpected code premise" end.'),
        ('resources', 'let rec introduce fuel := lazymatch fuel with | O => '
         'fail 100 "Resource preflight: structural budget exhausted" | S ?rest => '
         'liEnsureInvariant; lazymatch goal with | |- envs_entails _ (find_in_context (FindInstrKind ?address false) _) => '
         'constr_eq address constr:(' + literal + ') | |- envs_entails _ (_ -∗ _) => '
         'first [progress liUnfoldEarly | progress liWand]; introduce rest '
         '| |- envs_entails _ ?hidden => is_var hidden; lazymatch goal with '
         '| Hlocal := @LET_ID _ (find_in_context (FindInstrKind ?address false) _) |- _ => '
         'constr_eq Hlocal hidden; constr_eq address constr:(' + literal + '); '
         'liUnfoldLetGoal; introduce rest '
         '| _ => fail 100 "Resource preflight: unexpected continuation alias" end '
         '| _ => fail 100 "Resource preflight: unexpected structural goal" end end in introduce 4096%nat.'),
        ('lookup', 'lazymatch goal with | |- envs_entails _ '
         '(find_in_context (FindInstrKind ?address false) _) => constr_eq address constr:(' + literal +
         '); liFindInContext | _ => fail 100 "Resource preflight: wrong lookup goal" end.'),
        ('lookup-bound', 'lazymatch goal with | |- envs_entails _ '
         '(⌜is_Some (?lookup ?address)⌝ ∗ _) => '
         'constr_eq address constr:(' + literal + '); '
         'constr_eq lookup constr:(ZesuSsz.Contracts.SelectedCodeLookup.selectedCodeLookup ' + index + '); '
         'assert_fails (has_evar lookup); '
         'iSplit; [iPureIntro; change (is_Some ' + some + '); eexists; reflexivity |] '
         '| _ => fail 100 "Resource preflight: own-map membership obligation is absent" end.'),
        ('selected', 'lazymatch goal with | |- envs_entails ?environment '
         '(bi_pure (@eq (option isla_trace) ?actual ?wanted)) => '
         'assert_fails (has_evar actual); assert_fails (has_evar wanted); '
         'change (envs_entails environment (⌜' + some + ' = ' + some + '⌝)%I) '
         '| _ => fail 100 "Resource preflight: missing instruction or IKPre result" end.'),
        ('closed', 'iPureIntro; reflexivity.'),
    ]
    return {'entry': checked, 'resource': resource, 'index_source': index_source,
            'pc': pc, 'expected_instruction': expected, 'theorem': theorem,
            'source': probe, 'commands': [{'stage': stage, 'body': body} for stage, body in commands]}


def require_declarations(binding, plans, workspace):
    checked = entries.checked_file(binding, Path(workspace).resolve())
    receipt = json.loads(Path(checked['resolved']).read_bytes())
    if (receipt.get('passed') is not True or type(receipt.get('selected_entries')) is not int
            or receipt['selected_entries'] != len(plans)
            or type(receipt.get('checked_entries')) is not int
            or receipt['checked_entries'] != len(plans)
            or not isinstance(receipt.get('entries'), list)
            or len(receipt['entries']) != len(plans)):
        raise ValueError('All selected declarations must pass before resource checks.')
    for row, plan in zip(receipt['entries'], plans):
        entry = plan['entry']
        if (row.get('passed') is not True or row.get('id') != entry['id']
                or row.get('source') != entry['source'] or row.get('artifacts') != entry['artifacts']):
            raise ValueError('The declaration receipt differs from the resource inputs.')
    return checked


def one_goal(checked, empty=False):
    value = json.loads(Path(checked['resolved']).read_bytes())
    if (value['stack'] or value['shelf'] or value['given_up']
            or len(value['goals']) != (0 if empty else 1)):
        raise ValueError('The resource diagnostic has an unexpected goal group.')


async def check_resources(rows, declarations, workspace, function, output, session_factory):
    """Check fixed resource operations after the separate declaration stage."""
    workspace = Path(workspace).resolve(strict=True)
    output = Path(output).resolve()
    if not output.is_relative_to(workspace) or output.exists():
        raise ValueError('The resource preflight needs a fresh workspace output.')
    if not isinstance(rows, list) or not rows:
        raise ValueError('The resource preflight needs selected entries.')
    if any(not isinstance(row, dict) or set(row) != {'entry', 'resource'} for row in rows):
        raise ValueError('The resource preflight row has invalid fields.')
    entries.prepare_entries([row['entry'] for row in rows], workspace, function)
    plans = [make_plan(row['entry'], row['resource'], workspace, function) for row in rows]
    declaration_input = require_declarations(declarations, plans, workspace)
    output.mkdir(parents=True)
    results = []
    for plan in plans:
        entry = plan['entry']
        directory = output / entry['id']
        directory.mkdir()
        source = directory / 'ResourceLookup.v'
        source.write_text(plan['source'])
        source_input = entries.checked_file(entries.file_reference(source), workspace)
        (directory / 'COMMANDS.json').write_text(json.dumps(plan['commands'], indent=2) + '\n')
        journal = ToolJournal(directory / 'calls')
        result = {'id': entry['id'], 'passed': False, 'source': source_input,
                  'original_source': entry['source'], 'resource': plan['resource'],
                  'index_source': plan['index_source'],
                  'expected_instruction': plan['expected_instruction'], 'exports': [],
                  'pet': None, 'normal_context_closure': False, 'owned_pet_exited': False,
                  'primary_calls': 0, 'machine_instructions': 0}
        try:
            async with session_factory(directory) as session:
                try:
                    await journal.initialize(session)
                    async def call(tool, arguments):
                        if tool not in {'rocq_health', 'rocq_start', 'rocq_diag', 'rocq_query',
                                        'rocq_complete_goals', 'rocq_check'}:
                            raise ValueError('The resource diagnostic forbids this tool.')
                        if tool == 'rocq_check' and arguments.get('body') not in [row['body'] for row in plan['commands']]:
                            raise ValueError('The resource diagnostic forbids an arbitrary proof body.')
                        return entries.response_data(await journal.call_tool(session, tool, arguments))
                    health = await call('rocq_health', {})
                    if health.get('success') is not True or health.get('ok') is not True:
                        raise ValueError('The resource toolchain health check refused.')
                    started = await call('rocq_start', {'workspace': str(workspace), 'file': str(source),
                                                      'theorem': plan['theorem'], 'timeout': 60})
                    diagnostic = await call('rocq_diag', {})
                    if diagnostic.get('success') is not True:
                        raise ValueError('The owned resource diagnostic refused.')
                    result['pet'] = entries.process_identity(diagnostic.get('pet', {}).get('pid'))
                    state = started.get('state_id')
                    if started.get('success') is not True or type(state) is not int or state <= 0:
                        raise ValueError('The resource diagnostic declaration refused.')
                    for module, artifact in entry['artifacts'].items():
                        located = await call('rocq_query', {'from_state': state,
                            'command': 'Locate Library ' + module + '.', 'timeout': 60})
                        pattern = re.escape(module + ' has been loaded from file') + r'[ \t\r\n]+' + re.escape(artifact['resolved'])
                        if (located.get('success') is not True or type(located.get('from_state_id')) is not int
                                or located['from_state_id'] != state or not isinstance(located.get('output'), str)
                                or re.fullmatch(pattern, located['output'].strip()) is None):
                            raise ValueError('The resource diagnostic loaded a different object: ' + module)
                    async def export(stage, empty=False):
                        checked = entries.checked_export(await call('rocq_complete_goals', {'from_state': state}), state, directory)
                        one_goal(checked, empty)
                        result['exports'].append({'stage': stage, 'export': checked})
                    await export('entry')
                    for command in plan['commands']:
                        checked = await call('rocq_check', {'from_state': state, 'body': command['body'], 'timeout': 60})
                        state = checked.get('state_id')
                        if (checked.get('success') is not True or type(state) is not int or state <= 0
                                or type(checked.get('commands_run')) is not int or checked['commands_run'] != 1
                                or checked.get('proof_finished') is not (command['stage'] == 'closed')):
                            raise ValueError('The resource command refused: ' + command['stage'])
                        await export(command['stage'], command['stage'] == 'closed')
                    result['resource_checked'] = True
                except BaseException as error:
                    result['error'] = {'type': type(error).__name__, 'message': str(error)}
            result['normal_context_closure'] = True
        except BaseException as error:
            result['error'] = {'type': type(error).__name__, 'message': str(error)}
        finally:
            if result['pet'] is not None:
                deadline = time.monotonic() + 10
                while entries.matching_live(result['pet']) and time.monotonic() < deadline:
                    await asyncio.sleep(0.1)
                result['owned_pet_exited'] = not entries.matching_live(result['pet'])
            result['journal'] = journal.snapshot()
            result['passed'] = (result.get('resource_checked') is True
                                and result['normal_context_closure'] and result['owned_pet_exited']
                                and not result['journal']['retention_failed'])
            results.append(result)
            (directory / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
        if not result['passed']:
            break
    input_error = None
    try:
        entries.unchanged_file(declaration_input)
        for plan in plans:
            entries.unchanged_file(plan['entry']['source'])
            entries.unchanged_file(plan['index_source'])
            for artifact in plan['entry']['artifacts'].values():
                entries.unchanged_file(artifact)
        for result in results:
            entries.unchanged_file(result['source'])
            for exported in result['exports']:
                entries.unchanged_file(exported['export'])
    except (OSError, ValueError) as error:
        input_error = {'type': type(error).__name__, 'message': str(error)}
    receipt = {'schema': 1, 'passed': (input_error is None and len(results) == len(plans)
                                     and all(row['passed'] for row in results)),
               'declarations': declaration_input, 'entries': results,
               'selected_entries': len(plans), 'checked_entries': len(results),
               'input_error': input_error, 'primary_calls': 0, 'machine_instructions': 0,
               'scope': 'Selected-code registration, resource opening, and exact instruction lookup only.'}
    (output / 'REPORT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--mcp-command', required=True)
    args = parser.parse_args()
    value = json.loads(args.manifest.read_bytes())
    if (not isinstance(value, dict) or set(value) != {'schema', 'workspace', 'function', 'declarations', 'rows'}
            or type(value['schema']) is not int or value['schema'] != 1):
        parser.error('The resource manifest has an invalid schema.')
    workspace = Path(value['workspace']).resolve(strict=True)
    result = asyncio.run(check_resources(value['rows'], value['declarations'], workspace,
        value['function'], args.output, entries.owned_sessions(args.mcp_command, workspace)))
    print(json.dumps({'passed': result['passed'], 'report': entries.file_reference(args.output / 'REPORT.json'),
                      'primary_calls': 0, 'machine_instructions': 0}))
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
