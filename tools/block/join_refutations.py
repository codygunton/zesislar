"""Bind an infeasible source edge to a physically verified exact statement."""
import hashlib
import json
from pathlib import Path
import re

from entry_bindings import declared_binders
from witness_data import _source_definition, _unwrap, _words
from check_data_only_lemmas import rocq_tokens
from symbolic_state import Expr


def read(binding, *, document=False):
    path = Path(binding['path'])
    if not path.is_absolute():
        raise ValueError('A refutation binding needs an absolute source path')
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != binding['sha256']:
        raise ValueError('A refutation source binding changed')
    return json.loads(data) if document else data.decode()


def tokens(text):
    return _words(rocq_tokens(text))


def lemma(text, name):
    matched = re.search(r'\bLemma\s+' + re.escape(name) + r'\b.*?\.\s*Proof\.', text, re.S)
    if not matched:
        raise ValueError('The refutation statement is absent')
    return tokens(matched.group().rsplit('Proof.', 1)[0])


def validate_source_edge(row, edge):
    """Use the producer's exact retained/current register projection."""
    if row['state']['conditions'] != edge['original_conditions'] or row['path'] != edge['path']:
        raise ValueError('The refutation belongs to another source edge')
    registers = {**row['state'].get('retained_registers', {}), **row['state']['registers']}
    if any(registers.get(key) != value for key, value in edge['original_values'].items()):
        raise ValueError('The refutation changes an owned source value')


def validate_refutations(plan, refutations):
    """Return authenticated excluded indices; never infer infeasibility."""
    excluded = set()
    for item in refutations:
        if set(item) != {'edge', 'acceptance', 'source_assertion', 'domain_guard'}:
            raise ValueError('An edge refutation has unsupported fields')
        index = item['edge']
        if type(index) is not int or not 0 <= index < len(plan['edges']) or index in excluded:
            raise ValueError('An edge refutation has an invalid or duplicate index')
        accepted = read(item['acceptance'], document=True)
        verdict = {'success': True, 'verification_method': 'module_m', 'assumptions': []}
        if accepted['verdict'] != verdict:
            raise ValueError('The edge refutation lacks exact module_m acceptance')
        inputs = read(accepted['source_guards'], document=True)
        source = read(inputs['source'], document=True)
        row = source
        for part in inputs['alternative'].lstrip('/').split('/'):
            row = row[int(part)] if isinstance(row, list) else row[part]
        edge = plan['edges'][index]
        validate_source_edge(row, edge)
        body = _source_definition(item['source_assertion'])
        pure = []
        for position, token in enumerate(body):
            if token == '⌜':
                pure.append(_unwrap(body[position + 1:body.index('⌝', position + 1)]))
        if tokens(item['domain_guard']) not in pure:
            raise ValueError('The refutation domain is absent from the source assertion')
        source_text = read(item['source_assertion'])
        parameters = declared_binders(source_text, item['source_assertion']['declaration'])
        verification = read(accepted['verification'], document=True)
        compilation = read(accepted['compile'], document=True)
        if verification['result'] != verdict or not compilation['result'].get('success'):
            raise ValueError('The refutation compilation or verification failed')
        if compilation['arguments']['file'] != accepted['physical_source']['path']:
            raise ValueError('The compiler receipt names another refutation source')
        if compilation['arguments']['workspace'] != verification['arguments']['workspace']:
            raise ValueError('The refutation receipts use different workspaces')
        if Path(accepted['physical_source']['path']).with_suffix('.vo') != Path(accepted['physical_object']['path']):
            raise ValueError('The refutation object has another source identity')
        # Read every source and object binding before trusting either receipt.
        proof_source = read(accepted['physical_source'])
        object_path = Path(accepted['physical_object']['path'])
        if hashlib.sha256(object_path.read_bytes()).hexdigest() != accepted['physical_object']['sha256']:
            raise ValueError('The refutation object changed')
        read(inputs['domain'])
        for binding in accepted['domain_sources']:
            read(binding)
        name = verification['arguments']['problem_name']
        signature = ''.join(' (' + p['name'] + ' : ' + p['type'] + ')' for p in parameters)
        guards = [Expr.from_dict(row['state']['conditions'][i]).coq() + ' = true'
                  for i in inputs['guards']]
        expected = tokens('Lemma ' + name + signature + ' : ' +
                          ' -> '.join([item['domain_guard'], *guards, 'False']) + '.')
        if (lemma(verification['arguments']['problem_statement'], name) != expected or
                lemma(proof_source, name) != expected):
            raise ValueError('The verified refutation has different source assumptions')
        excluded.add(index)
    return excluded
