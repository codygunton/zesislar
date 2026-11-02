"""Check bounded project Ltac visibility without executing Rocq.

This is not semantic name resolution. Unsupported grammar, plugins, imports,
local bindings, and external sources produce unknown results, not acceptance.
"""
from pathlib import Path

from check_data_only_lemmas import IDENTIFIER, rocq_commands
from installed_mappings import require_imports
from entry_chain import binding, read_bound, save
from import_graph import graph_closure


COVERAGE = ('Project-defined Ltac references in ordinary Proof sentences and '
            'Ltac bodies, with plain Require/Import/Export and lexical modules. '
            'Unknown identifiers and unsupported syntax are not resolved. '
            'This check does not typecheck terms or execute tactics.')
QUOTATIONS = {'constr', 'uconstr', 'open_constr', 'type_term'}
HEAD_AFTER = {';', '|', '=>', 'then', 'else', 'in', '[', '(', '{', ':=',
              'try', 'tryif', 'repeat', 'first', 'solve', 'once', 'progress',
              'Fail', 'Time', 'Timeout', 'Proof', '-', '+', '*'}
MODIFIERS = {'Local', 'Global', 'Polymorphic', 'Monomorphic'}


def words_without_attributes(words):
    while words[:2] == ['#', '[']:
        try:
            words = words[words.index(']') + 1:]
        except ValueError:
            return []
    while words and words[0] in MODIFIERS:
        words = words[1:]
    return words


def document(module, source):
    """Retain source positions and explicit syntax coverage for one module."""
    text = source.read_text()
    commands = rocq_commands(text)
    definitions, imports, unknown, scopes = [], [], [], []
    for index, command in enumerate(commands):
        raw = [value for value, _ in command]
        words = words_without_attributes(raw)
        if not words:
            continue
        try:
            requested = require_imports(words, source)
        except ValueError:
            requested = None
            unknown.append((index, 'unsupported_import'))
        if requested is not None:
            mode = next((word for word in words[:4] if word in {'Import', 'Export'}), 'Require')
            imports.extend((index, row['module'], mode, True) for row in requested)
        elif words[0] in {'Import', 'Export'}:
            if all(IDENTIFIER.fullmatch(name) for name in words[1:]):
                imports.extend((index, name, words[0], False) for name in words[1:])
            else:
                unknown.append((index, 'unsupported_import'))
        if words[0] == 'Module':
            if len(words) == 2 and IDENTIFIER.fullmatch(words[1]):
                scopes.append(words[1])
            else:
                unknown.append((index, 'unsupported_module'))
        elif words[0] == 'End' and len(words) == 2 and scopes and words[1] == scopes[-1]:
            scopes.pop()
        elif words[0] == 'Ltac' and len(words) > 2 and ':=' in words:
            if (IDENTIFIER.fullmatch(words[1]) and '.' not in words[1] and
                    ':' not in words[2:words.index(':=')] and 'with' not in words):
                definitions.append({'name': '.'.join([module, *scopes, words[1]]),
                                    'short': words[1], 'scope': list(scopes), 'index': index, 'local': 'Local' in raw[:2]})
            else:
                unknown.append((index, 'unsupported_Ltac_definition'))
        elif (words[0] in {'Load', 'Include', 'Ltac2'} or
              words[:3] == ['Declare', 'ML', 'Module'] or words[:2] == ['Tactic', 'Notation']):
            unknown.append((index, 'unsupported_definition_mechanism'))
    return {'source': binding(source), 'text': text, 'commands': commands,
            'definitions': definitions, 'imports': imports, 'unknown': unknown}


def references(command, definitions):
    """Find known project tactic references outside explicit term quotations."""
    words = [value for value, _ in command]
    candidates, skip, depth = [], 0, 0
    declared = None
    simple = words_without_attributes(words)
    if simple[:1] == ['Ltac'] and ':=' in simple:
        declared = simple[1]
        start = words.index(':=') + 1
    else:
        start = 0
    # A local Ltac value can shadow a project name. Do not infer its type.
    local = set()
    for i, word in enumerate(words[:-1]):
        if word in {'let', 'fun'}:
            end = next((j for j in range(i + 1, len(words)) if words[j] in {':=', '=>'}), len(words))
            local.update(value for value in words[i + 1:end] if IDENTIFIER.fullmatch(value))
    if declared:
        local.update(simple[2:simple.index(':=')])
    for i in range(start, len(words)):
        word = words[i]
        if skip:
            if depth == -1:
                if word == '(':
                    depth = 1
            else:
                depth += (word in {'(', '[', '{'}) - (word in {')', ']', '}'})
                if depth == 0:
                    skip = 0
            continue
        if word in QUOTATIONS and words[i + 1:i + 3] == [':', '(']:
            skip, depth = 1, -1
            # The next '(' starts the quotation; the ':' is outside it.
            continue
        if i and words[i - 1] in QUOTATIONS and word == ':':
            continue
        if word in definitions and (i == start or words[i - 1] in HEAD_AFTER):
            candidates.append((word, command[i][1], word in local))
    return candidates


def inspect(ordered, documents):
    """Report every planned module before refusing any definite missing name."""
    names = {}
    for owner, doc in documents.items():
        for item in doc['definitions']:
            names.setdefault(item['short'], []).append((owner, item))
            parts = item['name'].split('.')
            for length in range(len(parts) - 1):
                names.setdefault('.'.join(parts[length:]), []).append((owner, item))
    def closure(initial, *, exported=False):
        found, todo = set(), list(initial)
        while todo:
            name = todo.pop()
            if name in found:
                continue
            found.add(name)
            if name in documents:
                todo.extend(target for _, target, mode, require in documents[name]['imports']
                            if mode == 'Export' or not exported and require)
        return found
    results = []
    for owner in ordered:
        doc = documents[owner]
        loaded, visible, local, calls, mechanisms = {owner}, set(), set(), [], []
        proof = False
        scopes = []
        imports_by_sentence = {}
        for row in doc['imports']:
            imports_by_sentence.setdefault(row[0], []).append(row)
        for index, command in enumerate(doc['commands']):
            words = [value for value, _ in command]
            simple = words_without_attributes(words)
            for _, target, mode, require in imports_by_sentence.get(index, []):
                if require:
                    loaded.update(closure([target]))
                elif target not in loaded:
                    mechanisms.append('unmodeled_module_import:' + target)
                if mode in {'Import', 'Export'}:
                    visible.update(closure([target], exported=True))
            mechanisms.extend(reason for position, reason in doc['unknown'] if position == index)
            if simple[:1] in [['Proof'], ['Goal']]:
                proof = True
            if simple[:1] == ['Module'] and len(simple) == 2:
                scopes.append(simple[1])
            elif simple[:1] == ['End'] and len(simple) == 2 and scopes and simple[1] == scopes[-1]:
                scopes.pop()
            is_ltac = simple[:1] == ['Ltac'] and ':=' in simple
            if proof or is_ltac:
                uncertain = set(mechanisms)
                for name in loaded - {owner}:
                    other = documents.get(name)
                    if other is None:
                        uncertain.add('unmodeled_import:' + name)
                    elif other['unknown']:
                        uncertain.add('unsupported_imported_mechanism:' + name)
                for name, offset, shadowed in references(command, names):
                    candidates = names[name]
                    qualified = '.' in name
                    matches = [(module, item) for module, item in candidates
                               if ((module == owner and item['scope'] == scopes[:len(item['scope'])] and
                                    (item['index'] < index or is_ltac and item['index'] == index))
                                   or not item['local'] and module in (loaded if qualified else visible))]
                    reasons = set(uncertain)
                    if shadowed:
                        reasons.add('local_value_binding')
                    if 'Fail' in words:
                        reasons.add('expected_failure_command')
                    if len(matches) > 1:
                        reasons.add('ambiguous_project_name')
                    status = ('unknown' if shadowed or len(matches) > 1 else
                              'visible' if matches else 'unknown' if reasons else 'missing')
                    calls.append({'name': name, 'line': doc['text'].count('\n', 0, offset) + 1,
                                  'project_visibility': bool(matches), 'status': status,
                                  'possible_owners': sorted({module for module, _ in candidates}),
                                  'unknown_reasons': sorted(reasons) if status == 'unknown' else []})
            for item in doc['definitions']:
                if item['index'] == index:
                    local.add(item['short'])
            if simple[:1] in [['Qed'], ['Defined'], ['Abort'], ['Admitted']]:
                proof = False
        results.append({'module': owner, 'source': doc['source'], 'calls': calls,
                        'unsupported': [{'sentence': index, 'reason': reason}
                                        for index, reason in doc['unknown']]})
    return {'schema': 'entry-chain.declaration-name-preflight.v1', 'coverage': COVERAGE,
            'complete_semantic_resolution': False, 'modules': results,
            'missing': [{'module': row['module'], **call} for row in results for call in row['calls']
                        if call['status'] == 'missing']}


def check(runtime, workspace, output):
    ordered = runtime.get('ordered_modules', [])
    if not ordered:
        return None
    graph = read_bound(runtime['cache_import_graph'])
    forward = {}
    for edge in graph['import_edges']:
        forward.setdefault(edge['from'], set()).add(edge['to'])
    required = graph_closure(ordered, forward)
    workspace = Path(workspace).resolve()
    documents = {}
    for name in sorted(required | set(ordered)):
        relative = runtime['module_files'].get(name)
        if relative is None:
            continue
        path = workspace / relative
        # External libraries retain normal compiler input authentication.
        if not path.resolve().is_relative_to(workspace) or not path.is_file():
            continue
        try:
            doc = document(name, path)
        except ValueError as error:
            doc = {'source': binding(path), 'text': '', 'commands': [], 'definitions': [],
                   'imports': [], 'unknown': [(0, 'unsupported_source_syntax: ' + str(error))]}
        documents[name] = doc
    missing_sources = set(ordered) - documents.keys()
    if missing_sources:
        raise ValueError('A planned declaration source is absent: ' + ', '.join(sorted(missing_sources)))
    report = inspect(ordered, documents)
    report['catalog_sources'] = [doc['source'] for doc in documents.values()]
    for reference in report['catalog_sources']:
        if binding(reference['path']) != reference:
            raise ValueError('A name-preflight source changed during inspection.')
    save(Path(output)/'DECLARATION-NAME-PREFLIGHT.json', report)
    if report['missing']:
        first = report['missing'][0]
        raise ValueError('A project Ltac call lacks a visible definition: ' + first['module'] +
                         ':' + str(first['line']) + ': ' + first['name'])
    return report
