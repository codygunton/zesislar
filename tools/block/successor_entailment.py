"""Validate designed successor handoffs without claiming native correctness."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import time
from datetime import datetime, timezone

import entry_schema
import chain_root
import setup_fallback
from chain_state import normalize_successor, render_successor

GROUPS = ('goals', 'stack', 'shelf', 'given_up')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def validate_import(module, binding, root):
    """Check direct modules or manifest-bound generated Dune modules."""
    if not entry_schema.ROCQ_NAME.fullmatch(module):
        raise ValueError('Invalid extra import name')
    root = Path(root)
    entry_schema.verify_sources({'source_hashes': {binding['path']: binding['sha256']}}, root)
    hashes = {binding['path']: binding['sha256']}
    if entry_schema.source_module(binding['path']) == module:
        return hashes
    theory, manifest = binding.get('theory'), binding.get('manifest')
    if not theory or not manifest:
        raise ValueError('The generated module lacks a theory or manifest binding')
    for value in (theory, manifest):
        entry_schema.verify_sources({'source_hashes': {value['path']: value['sha256']}}, root)
        hashes[value['path']] = value['sha256']
    theory_path = root / theory['path']
    source_path = root / binding['path']
    names = re.findall(r'\(coq\.theory\s+\(name\s+([\w.]+)\)', theory_path.read_text())
    if (len(names) != 1 or theory_path.name != 'dune' or
            source_path.parent != theory_path.parent or
            module != names[0] + '.' + source_path.stem):
        raise ValueError('The generated module disagrees with its Dune theory')
    recipe = json.loads((root / manifest['path']).read_text())
    artifact = recipe.get('project_derived', {}).get(binding['path'], {})
    if (artifact.get('sha256') != binding['sha256'] or
            artifact.get('path') != binding['path'] or
            artifact.get('artifact_identity') != recipe.get('artifact_identity') or
            not recipe.get('artifact_identity')):
        raise ValueError('The generated import disagrees with its selected manifest')
    return hashes


def debt_groups(value):
    """Retain all returned groups; missing fields never mean empty debts."""
    for key in GROUPS:
        if key not in value or not isinstance(value[key], list):
            raise ValueError('Unavailable goal group: ' + key)
    for frame in value['stack']:
        if (not isinstance(frame, list) or len(frame) != 2 or
                not all(isinstance(side, list) for side in frame)):
            raise ValueError('Unavailable stack sides')
    groups = {key: deepcopy(value[key]) for key in GROUPS}
    payload = json.dumps(groups, sort_keys=True, separators=(',', ':'),
                         ensure_ascii=False, allow_nan=False).encode()
    return {'groups': groups, 'sha256': hashlib.sha256(payload).hexdigest(),
            'counts': {key: len(value[key]) for key in GROUPS},
            'stack_sides': [{'left': len(frame[0]), 'right': len(frame[1])}
                            for frame in value['stack']],
            'empty': not any(value[key] for key in GROUPS)}


def designed_target(block, root):
    """Bind executable names and ordered arguments to their declared sources."""
    fields = entry_schema.contract_fields(block)
    if fields is None:
        raise ValueError('Unavailable designed successor entry')
    root = entry_schema.verify_sources(fields, root)
    for key in ('entry_definition', 'resource_predicate'):
        name = fields[key]
        owners = [path for path in fields['source_hashes'] if path.endswith('.v')
                  and name.startswith(entry_schema.source_module(path) + '.')]
        if not owners:
            raise ValueError('Unbound executable name: ' + name)
        owner = max(owners, key=lambda path: len(entry_schema.source_module(path)))
        if not re.search(r'\bDefinition\s+' + re.escape(name.rsplit('.', 1)[-1]) + r'\b',
                         (root / owner).read_text()):
            raise ValueError('Missing executable Definition: ' + name)
    pc = block['entry_pc']
    pc = int(pc, 0) if isinstance(pc, str) else pc
    return {'entry_pc': hex(pc), **fields,
            'application': fields['resource_predicate'] + ''.join(
                ' (' + argument + ')' for argument in fields['arguments'])}


def capture_evidence(capture, exported, expected_provenance):
    """Validate recorder evidence while keeping every inherited debt explicit."""
    if capture.get('outcome') != 'reached':
        raise ValueError('The native capture did not reach its stop')
    if not expected_provenance or capture.get('root_provenance') != expected_provenance:
        raise ValueError('Missing or incompatible root provenance')
    if capture.get('provenance') and capture['provenance'] != expected_provenance:
        raise ValueError('Inconsistent root provenance')
    if (not isinstance(capture.get('inherited_debts'), dict) or
            not isinstance(capture.get('pending_goals'), list) or
            not isinstance(capture.get('shelved_goals'), list)):
        raise ValueError('Unavailable inherited or capture debts')
    if not exported.get('success') or exported.get('checkpoint') != 'recorders':
        raise ValueError('Unavailable recorder goal groups')
    if exported.get('scope') != 'native checkpoint':
        raise ValueError('The export is not a native checkpoint')
    if not exported.get('owned_pet_pid') or exported.get('state_id') is None:
        raise ValueError('The export lacks an owned native state')
    path = Path(exported['path'])
    if digest(path) != exported['sha256']:
        raise ValueError('The goal export hash changed')
    source = Path(exported['source'])
    if digest(source) != exported['source_sha256']:
        raise ValueError('The native source hash changed')
    if capture.get('source_sha256') != exported['source_sha256']:
        raise ValueError('The capture and export use different sources')
    if digest(source.with_suffix('.mcp.json')) != exported['primary_capture_sha256']:
        raise ValueError('The primary capture hash changed')
    debts = debt_groups(json.loads(path.read_text()))
    return {'native_debts': debts,
            'inherited_debts': deepcopy(capture.get('inherited_debts', {})),
            'pending_goals': deepcopy(capture.get('pending_goals', [])),
            'shelved_goals': deepcopy(capture.get('shelved_goals', [])),
            'export': deepcopy(exported), 'contract_closed': False}


def plan_successor(capture, block, root, exported, expected_provenance, *, root_parameters):
    """Prepare an entailment target; leave quantifier and proof decisions explicit."""
    target = designed_target(block, root)
    if capture.get('exit') != target['entry_pc']:
        raise ValueError('The capture stopped at a different successor')
    evidence = capture_evidence(capture, exported, expected_provenance)
    return {'target': target, 'evidence': evidence,
            'binders': capture['binders'], 'contract_closed': False,
            'root_parameters': list(root_parameters),
            'proof_status': 'unproved',
            'scope': 'Captured-resource entailment is separate from native correctness'}


def successor_application(target, fixed_binders, root_parameters):
    """Bind new data witnesses inside iProp; keep every entry parameter fixed."""
    fixed = chain_root.gen_block.gen_boundary.binder_types(fixed_binders)
    locals_, substitutions = [], {}
    for binder in target['binders']:
        name, kind = binder['name'], binder['type']
        if name in root_parameters:
            if name not in fixed:
                raise ValueError('A root successor parameter is unavailable: ' + name)
            if fixed[name] != kind:
                raise ValueError('A fixed successor parameter changed type: ' + name)
        else:
            if kind in {'Prop', 'Type', 'Set'}:
                raise ValueError('A successor witness is not a data parameter: ' + name)
            fresh = 'successor_' + name
            while fresh in fixed or fresh in substitutions.values():
                fresh = 'successor_' + fresh
            substitutions[name] = fresh
            locals_.append((fresh, kind))
    def substitute(text):
        for old, new in substitutions.items():
            text = re.sub(r"(?<![\w'.])" + re.escape(old) + r"(?![\w'])",
                          lambda _: new, text)
        return text
    body = substitute(target['application'])
    if locals_:
        body = '∃ ' + ' '.join(f'({name} : {substitute(kind)})' for name, kind in locals_) + ', ' + body
    return '(' + body + ')%I'


def successor_root_parameters(design):
    """Keep declared interface parameters fixed across successor applications."""
    root = chain_root.gen_block.address(design['entry_pc'])
    entry = next(row for row in design['blocks']
                 if chain_root.gen_block.address(row['entry_pc']) == root)
    names = [binder['name'] for binder in entry['binders']]
    selected = design.get('table_convention', {}).get('successor_root_parameters', names)
    if (not isinstance(selected, list) or any(not isinstance(name, str) for name in selected)
            or len(selected) != len(set(selected))
            or selected != [name for name in names if name in selected]):
        raise ValueError('The successor root parameters must be an ordered subset of the root binders')
    return list(selected)


def native_boundary_source(state, block, design, root, *, enabled=True,
                           terminal=None, extra_imports=(), historical_target=None):
    """Use the existing whole-block renderer with actual designed boundaries.

    The disabled source is the unchanged abstract-stop probe. The enabled
    source is a new proof obligation, not a changed historical measurement.
    Terminal descriptors name an existing full-result obligation explicitly.
    """
    entry = chain_root.gen_block.address(block['start'])
    entries = {chain_root.gen_block.address(row['entry_pc']): row
               for row in design['blocks']}
    convention = design.get('table_convention', {})
    if convention.get('existential_binders') != "Each row's binders, in their listed order":
        raise ValueError('Unavailable published binder convention')
    root_parameters = successor_root_parameters(design)
    if entry not in entries:
        raise ValueError('The native block has no designed entry')
    original = designed_target(entries[entry], root)
    if state.get('root_provenance') != entry_schema.contract_fields(entries[entry]):
        raise ValueError('The native entry provenance changed')
    if state.get('coq') or state.get('spatial') != [original['application']]:
        raise ValueError('The native proof must start from its designed entry')
    expected_binders = "`{!islaG Sigma} `{!threadG}" + ''.join(
        f" ({item['name']} : {item['type']})" for item in original['binders'])
    if state['binders'] != expected_binders:
        raise ValueError('The native entry parameters changed')
    successors = [chain_root.gen_block.address(pc) for pc in block['successors']]
    if not successors:
        if terminal is None:
            raise ValueError('Unavailable terminal Level1 obligation')
        target = chain_root.terminal_target(terminal['address'])
    else:
        target = successors[0]
    source = chain_root.render_probe(state, block, target)
    if not enabled:
        if historical_target is not None:
            source = chain_root.render_probe(state, block, historical_target)
        return {'source': source, 'lemma': 'infer_boundary',
                'scope': 'unchanged abstract-stop diagnostic', 'contract_closed': False}
    name = f'DesignedBoundary_{entry:x}'
    position = source.index('Lemma infer_boundary ')
    end = source.index('\nProof.\n', position)
    prefix, statement = source[:position], source[position:end]
    imports = list(extra_imports)
    if not successors:
        if terminal.get('kind') != 'owned_continuation':
            raise ValueError('Image-only terminal obligations cannot close the native boundary')
        declaration = designed_target({'entry_pc': hex(entry),
            'entry_definition': terminal['definition'],
            'resource_predicate': terminal['definition'], 'binders': [], 'arguments': [],
            'source_hashes': terminal['source_hashes']}, root)
        imports.extend(entry_schema.source_module(path) for path in declaration['source_hashes'] if path.endswith('.v'))
        marker = chain_root.boundary_stop(target)
        binder = f' ({marker} : iProp Sigma)'
        premise = f'  instr_pre ({target}) {marker} -∗\n'
        if statement.count(binder) != 1 or statement.count(premise) != 1:
            raise ValueError('The native terminal statement changed')
        statement = statement.replace(binder, '').replace(premise, '')
        statement = statement.replace('Lemma infer_boundary ', f'Lemma {name} ', 1)
    else:
        for pc in successors:
            if pc not in entries:
                raise ValueError('The CFG successor has no designed entry: ' + hex(pc))
            successor = designed_target(entries[pc], root)
            marker = chain_root.boundary_stop(pc)
            binder = f' ({marker} : iProp Sigma)'
            if statement.count(binder) != 1:
                raise ValueError('The native statement lacks a unique successor binder')
            statement = statement.replace(binder, '')
            statement = re.sub(r'\b' + re.escape(marker) + r'\b',
                               lambda _: successor_application(successor, state['binders'], root_parameters), statement)
            imports.extend(entry_schema.source_module(path) for path in successor['source_hashes'] if path.endswith('.v'))
        statement = statement.replace('Lemma infer_boundary ', f'Lemma {name} ', 1)
    if re.search(r'\b(?:BLK_STOP_|CHAIN_STOP_)', statement):
        raise ValueError('An arbitrary continuation remains in the native statement')
    headers = ''.join('Require Import ' + module + '.\n' for module in dict.fromkeys(imports))
    # No captured pure fact or execution result becomes a premise here.
    proof = '\nProof.\n  try zesu_block.\nQed.\n\nPrint Assumptions ' + name + '.\n'
    return {'source': prefix + headers + statement + proof, 'lemma': name,
            'entry_pc': hex(entry), 'entry_definition': original['entry_definition'],
            'statement_sha256': hashlib.sha256(statement.encode()).hexdigest(),
            'successors': [hex(pc) for pc in successors],
            'root_parameters': root_parameters,
            'terminal_scope': 'existing owned Level1 continuation; no added image continuation' if not successors else None,
            'scope': 'unproved native designed boundary', 'contract_closed': False}


def capture_entailment_source(capture, plan, *, extra_imports=None, root=None):
    """Render resource subsumption separately from the native boundary proof."""
    target = plan['target']
    post = normalize_successor(capture, entry=target['entry_pc'],
                               binders=plan['binders'], name='CapturedSuccessor',
                               provenance=capture['root_provenance'])
    post['imports'].extend(entry_schema.source_module(path)
                           for path in target['source_hashes'] if path.endswith('.v'))
    bound_imports = {}
    for module, binding in (extra_imports or {}).items():
        if root is None:
            raise ValueError('The extra import lacks an exact source binding')
        bound_imports.update(validate_import(module, binding, root))
        post['imports'].append(module)
    arguments = chain_root.gen_block.gen_boundary.explicit_arguments(plan['binders'])
    source = render_successor(post)
    name = 'designed_successor_entailment'
    source = 'Require Import ZesuSsz.Automation.All.\n' + source
    source += (f'\nLemma {name} {plan["binders"]} :\n'
               f'  CapturedSuccessor {arguments} -∗ '
               f'{successor_application(target, plan["binders"], plan["root_parameters"])}.\n'
               'Proof.\n  unfold CapturedSuccessor.\n  try zesu_block.\nQed.\n'
               f'Print Assumptions {name}.\n')
    return {'source': source, 'lemma': name, 'scope': 'capture entailment only',
            'contract_closed': False, 'bound_imports': bound_imports}


def _result(value):
    if isinstance(value, dict):
        return value
    if value.structuredContent is not None:
        return value.structuredContent
    for item in value.content:
        if getattr(item, 'type', None) == 'text':
            try:
                return json.loads(item.text)
            except ValueError:
                pass
    return {'success': False, 'error': 'The MCP call returned no structured result'}


async def check_boundary(session, rendered, path, workspace, *, inherited_debts,
                         seconds=1200, session_identity=None):
    """Require kernel evidence and complete empty groups before native closure.

    The caller owns the guarded MCP session and its compiler worker budget.
    Capture entailments use this checker but can never claim native closure.
    """
    if not 0 < seconds <= 1200:
        raise ValueError('The proof budget must be between 1 and 1200 seconds')
    if not isinstance(inherited_debts, dict):
        raise ValueError('Inherited debts must be explicit')
    path = Path(path).resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(rendered['source'])
    record = {'source': str(path), 'source_sha256': digest(path),
              'lemma': rendered['lemma'], 'scope': rendered['scope'],
              'inherited_debts': deepcopy(inherited_debts), 'calls': [],
              'outcome': 'unavailable', 'contract_closed': False, 'block_closed': False,
              'terminal_scope': rendered.get('terminal_scope'), 'exports': [],
              'entry_pc': rendered.get('entry_pc'),
              'entry_definition': rendered.get('entry_definition'),
              'successors': deepcopy(rendered.get('successors', [])),
              'statement_sha256': rendered.get('statement_sha256')}

    async def call(tool, arguments):
        started = time.monotonic()
        stamp = datetime.now(timezone.utc).isoformat()
        try:
            result = _result(await session.call_tool(tool, arguments))
        except Exception as error:
            result = {'success': False, 'error': str(error), 'reason': 'transport_exception'}
        row = {'tool': tool, 'arguments': arguments, 'result': result,
               'started': stamp, 'elapsed_seconds': time.monotonic() - started}
        if tool == 'rocq_check':
            # Both accepted proof stages contain exactly one SDK sentence.
            row['sentence_budgets'] = [{'sentence_sha256': hashlib.sha256(arguments['body'].encode()).hexdigest(),
                                       'timeout_seconds': arguments['timeout'],
                                       'effective_timeout_seconds': result.get('clamped_timeout', arguments['timeout'])
                                           if 'success' in result else None}]
        record['calls'].append(row)
        return result

    async def export(current, label):
        exported = await call('rocq_complete_goals', {'from_state': current['state_id']})
        if not exported.get('success') or digest(exported['path']) != exported['sha256']:
            raise ValueError('Unavailable complete goal export: ' + label)
        groups = debt_groups(json.loads(Path(exported['path']).read_text()))
        record['exports'].append({**exported, 'checkpoint': label, 'debt_groups': groups,
                                  'source_sha256': record['interactive_source_sha256'],
                                  'source': record['interactive_source'],
                                  'state_id': current['state_id'],
                                  'session_directory': str(Path(exported['path']).parent),
                                  'session_identity': deepcopy(session_identity)})
        return groups

    try:
        if rendered['scope'] == 'unproved native designed boundary':
            lemma_start = rendered['source'].index('Lemma ' + rendered['lemma'])
            proof_start = rendered['source'].index('\nProof.\n', lemma_start)
            statement = rendered['source'][lemma_start:proof_start]
            if (not rendered.get('entry_pc') or not rendered.get('entry_definition') or
                    hashlib.sha256(statement.encode()).hexdigest() != rendered.get('statement_sha256') or
                    not re.search(r'\binstr_body\s+' + re.escape(rendered['entry_pc']) + r'\b', statement)):
                raise ValueError('Unavailable native boundary signature')
        interactive_path = setup_fallback.write_interactive_source(path)
        record['interactive_source'] = str(interactive_path)
        record['interactive_source_sha256'] = digest(interactive_path)
        health = await call('rocq_health', {})
        if not health.get('ok'):
            return dict(record, residual_class='toolchain_unavailable')
        opened = await call('rocq_start', {'workspace': str(workspace), 'file': str(interactive_path),
                            'theorem': rendered['lemma'], 'timeout': 60})
        if not opened.get('success'):
            return dict(record, residual_class='entry_unavailable')
        if session_identity is None:
            diagnostic = await call('rocq_diag', {})
            session_identity = {'owned_pet_pid': diagnostic.get('pet', {}).get('pid')}
        if not session_identity.get('owned_pet_pid'):
            return dict(record, residual_class='session_identity_unavailable')
        await export(opened, 'entry')
        body = rendered['source'].split('Lemma ' + rendered['lemma'], 1)[1].split('\nProof.\n', 1)[1].split('\nQed.', 1)[0]
        if body.count('try zesu_block.') != 1:
            raise ValueError('The proof lacks a unique isolated primary sentence')
        preparation, tail = body.split('try zesu_block.', 1)
        if tail.strip():
            raise ValueError('The native proof contains unmeasured recorder commands')
        if preparation.strip():
            if preparation.strip() != 'unfold CapturedSuccessor.':
                raise ValueError('The proof contains an unapproved preparation stage')
            opened = await call('rocq_check', {'from_state': opened['state_id'],
                                'body': preparation.strip(), 'timeout': 60})
            if not opened.get('success'):
                return dict(record, outcome='residual', residual_class='proof_preparation')
        await export(opened, 'preparation')
        checked = await call('rocq_check', {'from_state': opened['state_id'],
                             'body': 'try zesu_block.', 'timeout': seconds})
        if not checked.get('success'):
            return dict(record, outcome='residual', residual_class='native_automation',
                        failed_transaction=checked)
        record['debt_groups'] = await export(checked, 'primary')
        if not record['debt_groups']['empty']:
            return dict(record, outcome='residual', residual_class='remaining_debts')
        if digest(path) != record['source_sha256']:
            raise ValueError('The native proof source changed')
        compiled = await call('rocq_compile_file', {'workspace': str(workspace),
                              'file': str(path), 'timeout': seconds, 'timing': True})
        if not compiled.get('success'):
            return dict(record, outcome='residual', residual_class='kernel_compilation')
        lemma_position = rendered['source'].index('Lemma ' + rendered['lemma'])
        proof_position = rendered['source'].index('\nProof.\n', lemma_position)
        statement = rendered['source'][:proof_position] + '\nAdmitted.\n'
        verified = await call('rocq_verify', {'workspace': str(workspace),
                              'problem_name': rendered['lemma'],
                              'problem_statement': statement,
                              'proof': rendered['source'], 'timeout': seconds})
        if not verified.get('success') or verified.get('assumptions') != []:
            return dict(record, outcome='residual', residual_class='kernel_verification')
        if digest(path) != record['source_sha256']:
            raise ValueError('The verified proof source changed')
        record['entailment_verified'] = True
        if any(inherited_debts.values()):
            return dict(record, outcome='conditional', residual_class='inherited_debts')
        native = rendered['scope'] == 'unproved native designed boundary'
        return dict(record, outcome='verified', block_closed=native, residual_class=None)
    except (OSError, ValueError, KeyError, TypeError) as error:
        return dict(record, error=str(error), residual_class='evidence_unavailable')
