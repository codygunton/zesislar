"""Bind a declaration-only compile before the native start or search."""
from pathlib import Path
import hashlib

from entry_chain import binding, digest, read_bound, save
from scratch_statement import source_statement


def declaration_search_fixture(source, specification, output, side):
    original_sha = digest(source)
    problem = specification['prefix'] + specification['statement'] + specification.get('pre_proof_commands', '')
    if not problem.endswith('\n'):
        raise ValueError('The native declaration must end before its Proof line.')
    fixture = source.with_name(source.stem + '_EntryPilotSearch.v')
    with fixture.open('x') as stream:
        stream.write(problem + 'Proof.\nAbort.\n')
    proof_line = problem.count('\n')
    if fixture.read_text().splitlines()[proof_line] != 'Proof.':
        raise ValueError('The search cursor does not select its Proof sentence.')
    if digest(source) != original_sha:
        raise ValueError('The search fixture changed its native source.')
    save(Path(output)/(side+'-SEARCH-FIXTURE.json'), {
        'original_source': str(source), 'original_source_sha256': original_sha,
        'prefix_sha256': hashlib.sha256(specification['prefix'].encode()).hexdigest(),
        'statement_sha256': hashlib.sha256(specification['statement'].encode()).hexdigest(),
        'fixture': str(fixture), 'fixture_sha256': digest(fixture),
        'line': proof_line, 'character': len('Proof.')-1, 'suffix': 'Proof.\nAbort.\n'})
    return fixture, proof_line


def prepare(runtime, workspace, output):
    from native_route import authority_body
    target = runtime['target']['block']
    source = Path(workspace)/runtime['module_files'][target['module']]
    if digest(source) != target['source_sha256']:
        raise ValueError('The native preflight source changed.')
    route = runtime.get('native_route')
    specification = source_statement(source, authority_body(route) if route else 'zesu_block.')
    if hashlib.sha256(specification['statement'].encode()).hexdigest() != target['statement_sha256']:
        raise ValueError('The native preflight statement changed.')
    Path(output).mkdir(exist_ok=True)
    fixture, _ = declaration_search_fixture(source, specification, Path(output), 'block')
    runtime['native_parse_preflight'] = binding(Path(output)/'block-SEARCH-FIXTURE.json')
    return fixture


def checked_fixture(runtime, workspace, source, specification):
    reference = runtime.get('native_parse_preflight')
    if not isinstance(reference, dict):
        raise ValueError('The native runtime lacks its bound declaration preflight.')
    value = read_bound(reference)
    fixture = source.with_name(source.stem + '_EntryPilotSearch.v')
    expected = specification['prefix'] + specification['statement'] + specification.get('pre_proof_commands', '')
    expected += 'Proof.\nAbort.\n'
    if (value['original_source'] != str(source) or value['original_source_sha256'] != digest(source)
            or value['fixture'] != str(fixture) or value['fixture_sha256'] != digest(fixture)
            or fixture.read_text() != expected or not fixture.resolve().is_relative_to(Path(workspace).resolve())
            or value['line'] != expected[:-len('Proof.\nAbort.\n')].count('\n') or value['character'] != 5):
        raise ValueError('The bound declaration preflight differs from its native source.')
    return fixture, value['line']
