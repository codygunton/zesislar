#!/usr/bin/env python3
"""Count per-function source text at a commit without running a proof."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from residual.modules import parse_module
from launch_imports import require_modules
from check_data_only_lemmas import command_imports, rocq_commands


MANIFEST = 'ZesuSsz/Evidence/decodeItem_function_text.json'
HAND_CHECKPOINT = 'build/stock-zisk/automation-validation/hand-kinds/CHECKPOINT.json'
KINDS = ('machine', 'trace_return', 'encoding', 'branch', 'spatial', 'finishing')
KIND_LABEL = 'kind counts v2 (replacement classifier, 2026-10-19)'
# These lists are fixed source-text cues. They do not establish tactic execution.
TOKENS = {
    'machine': ('liAStep', 'liARun', 'liStep', 'liRun', 'liTrace', 'liTraceS',
                'liAStepS', 'liARunS', 'zesu_block', 'zesu_run_until', 'zesu_run',
                'zesu_run_pass_steps', 'li_wp', 'li_wp_read_mem', 'li_wp_write_mem'),
    'trace_return': ('spec_trace', 'spec_instr_resources', 'instr_pre', 'instr_body',
                     'instr_lookup_resources', 'FindInstrKind', 'normalize_instr_addr',
                     'solve_normalize_instr_addr', 'normalize_instr_addr_riscv64_ret_tac'),
    'encoding': ('ResultImage', 'fieldImage', 'littleEndian', 'bigEndian',
                 'bv_extract', 'bv_concat', 'bv_zero_extend', 'bv_sign_extend',
                 'Z.land', 'Z.lor', 'Z.shiftl', 'Z.shiftr'),
    'branch': ('destruct', 'case_destruct', 'case', 'iExists', 'iSplit', 'iSplitL',
               'iSplitR', 'left', 'right'),
    'spatial': ('iIntros', 'iDestruct', 'iFrame', 'iRename', 'iApply', 'iPoseProof',
                'iExact', 'iModIntro', 'iEval', 'iMatchHyp', 'liExist', 'liWand',
                'FindHypEqual', 'FindMemMapsTo', 'ZesuMemRegionSearch',
                'find_mem_region_array', 'reg_col', '↦ₘ', '↦ₘ∗', '↦ᵣ'),
    'finishing': ('lia', 'nia', 'bv_solve', 'bv_simplify', 'reflexivity', 'done',
                  'assumption', 'congruence', 'discriminate', 'simpl', 'cbn',
                  'rewrite', 'unfold', 'unLET', 'subst', 'clear', 'pose', 'assert'),
}
TOKEN_PATTERNS = {
    kind: tuple(re.compile(r'(?<![A-Za-z0-9_])' + re.escape(token) +
                           r'(?![A-Za-z0-9_])') for token in tokens)
    for kind, tokens in TOKENS.items()
}
STRUCTURAL = re.compile(r'^(?:[{}[\]|+*\-]+|\d+\s*:|(?:all|shelve)\s*:)\s*\.?$')


def classify_lines(lines):
    """Use fixed cues, then inherit the next kind for structural lines."""
    direct, mixed = [], 0
    for line in lines:
        stripped = line.strip()
        if not stripped or STRUCTURAL.fullmatch(stripped) or stripped.startswith('(*'):
            direct.append(None)
            continue
        matches = [kind for kind in KINDS if any(pattern.search(line) for pattern in TOKEN_PATTERNS[kind])]
        direct.append(matches[0] if matches else 'other')
        mixed += len(matches) >= 2
    counts, structural = Counter(), 0
    for index, line in enumerate(lines):
        if not line.strip():
            continue
        kind = direct[index]
        if kind is None:
            structural += 1
            kind = next((value for value in direct[index + 1:] if value is not None), None)
        if kind is None:
            kind = next((value for value in reversed(direct[:index]) if value is not None), 'other')
        counts[kind] += 1
    return {kind: counts[kind] for kind in (*KINDS, 'other')}, mixed, structural


TEXT_CATEGORIES = ('contracts', 'introductions', 'exit_meanings', 'loop_steps', 'registrations', 'generator_json', 'block_proofs', 'composition', 'tests_and_exports')
PROOF_CATEGORIES = {'contracts', 'introductions', 'exit_meanings', 'loop_steps', 'registrations'}
# Reviewed capability modules. Names alone do not classify other modules.
CALL_SPEC_MODULES = {
    'ZesuSsz/Contracts/DecodeItemCallSpec.v': 'Machine-call boundary contract',
    'ZesuSsz/Compliance/DecodeItemCallSpec.v': 'Derived machine-call specification',
    'ZesuSsz/Contracts/DecodeItemCompositional.v': 'Compositional call boundary',
    'ZesuSsz/Compliance/DecodeItemCompositionalBridge.v': 'Bridge to the compositional call boundary',
    'ZesuSsz/Compliance/DecodeItemCompositionalCompliance.v': 'Compositional compliance proof',
    'ZesuSsz/Compliance/DecodeItemCompositionalWeakening.v': 'Call-exit resource weakening',
}



class Commit:
    def __init__(self, root, revision):
        self.root = Path(root)
        self.sha = self.git('rev-parse', '--verify', '--end-of-options', revision + '^{commit}').strip()
        self.paths = set(self.git('ls-tree', '-r', '--name-only', self.sha).splitlines())

    def git(self, *arguments):
        return subprocess.check_output(['git', '-C', str(self.root), *arguments], text=True)

    def read(self, path):
        if path not in self.paths:
            raise ValueError('The commit does not contain ' + path)
        return subprocess.check_output(['git', '-C', str(self.root), 'show', self.sha + ':' + path])


def range_count(lines, ranges):
    selected = set()
    for first, last in ranges:
        if not 1 <= first <= last <= len(lines):
            raise ValueError('A manifest range is outside its file.')
        selected.update(range(first - 1, last))
    return len(selected)


def boundary_counts(commit, path, directory):
    temporary = Path(directory) / Path(path).name
    temporary.write_bytes(commit.read(path))
    proofs = [proof for proof in parse_module(temporary) if proof.name.startswith('DesignedBoundary_')]
    expected = 'DesignedBoundary_' + Path(path).stem.removeprefix('Block')
    if len(proofs) != 1 or proofs[0].name != expected:
        raise ValueError('The block must contain its exact boundary theorem: ' + path)
    proof = proofs[0]
    native = proof.automation_only
    kinds, mixed, structural = classify_lines(proof.hand_lines) if not native else (dict.fromkeys((*KINDS, 'other'), 0), 0, 0)
    return dict(path=path, status='native' if native else 'hand',
                lines=0 if native else len(proof.hand_lines), kinds=kinds,
                mixed_lines=mixed, structural_lines=structural)


def block_counts(commit, directory):
    groups = {}
    for path in sorted(commit.paths):
        match = re.fullmatch(r'ZesuSsz/Proofs/DecodeItem/(?:Hand|Auto)/Block([0-9a-fA-F]+)(Literal|ShortString)?\.v', path)
        if not match:
            continue
        pc, branch = match[1].lower(), match[2] or ''
        group = groups.setdefault(pc, {})
        if branch in group:
            raise ValueError('The commit repeats a block module: ' + pc)
        group[branch] = path
    blocks = []
    for pc, group in sorted(groups.items()):
        if set(group) == {''}:
            blocks.append(dict(pc=pc, **boundary_counts(commit, group[''], directory)))
            continue
        if set(group) != {'', 'Literal', 'ShortString'}:
            raise ValueError('The split block requires its umbrella and both branches: ' + pc)
        umbrella = group['']
        if any(Path(path).parent != Path(umbrella).parent for path in group.values()):
            raise ValueError('Split modules must share their umbrella directory: ' + pc)
        exports = set()
        for command in rocq_commands(commit.read(umbrella).decode()):
            values = [token for token, _ in command]
            if not values or (values[0] != 'Require' and not (values[0] == 'From' and 'Require' in values)):
                raise ValueError('A split umbrella must contain only Require commands: ' + umbrella)
            imported, exported = command_imports(values)
            if exported:
                exports.update(imported)
        branches = [boundary_counts(commit, group[name], directory) for name in ('Literal', 'ShortString')]
        required = {'.'.join(Path(row['path']).with_suffix('').parts) for row in branches}
        if not required <= exports:
            raise ValueError('The split umbrella must export both branches: ' + umbrella)
        blocks.append(dict(pc=pc, path=umbrella, branches=branches,
                           status='native' if all(row['status'] == 'native' for row in branches) else 'hand',
                           lines=sum(row['lines'] for row in branches),
                           kinds={kind: sum(row['kinds'][kind] for row in branches) for kind in (*KINDS, 'other')},
                           mixed_lines=sum(row['mixed_lines'] for row in branches),
                           structural_lines=sum(row['structural_lines'] for row in branches)))
    return blocks, {path for group in groups.values() for path in group.values()}


def count_legacy_commit(commit):
    manifest = json.loads(commit.read(MANIFEST))
    checkpoint = json.loads(commit.read(HAND_CHECKPOINT))
    hand_lines = 0
    kind_totals = Counter()
    mixed_total = structural_total = 0
    with tempfile.TemporaryDirectory(prefix='lithium-metrics-') as directory:
        blocks, block_paths = block_counts(commit, directory)
    for row in blocks:
        hand_lines += row['lines']
        kind_totals.update(row['kinds'])
        mixed_total += row['mixed_lines']
        structural_total += row['structural_lines']
    if len({row['pc'] for row in blocks}) != len(blocks) or len(blocks) != 24:
        raise ValueError('The commit must contain exactly 24 distinct blocks.')
    categories = Counter()
    block_support = Counter()
    composition_lines = 0
    changed_mixed = []
    listed = set()
    for row in manifest['files']:
        path, category = row['path'], row['category']
        if category not in TEXT_CATEGORIES or row['scope'] not in ('whole_file', 'mixed_file'):
            raise ValueError('The manifest has an unknown category or scope: ' + path)
        if path in listed:
            raise ValueError('The manifest repeats a path: ' + path)
        listed.add(path)
        data = commit.read(path)
        lines = data.splitlines()
        if row['scope'] == 'whole_file':
            count = len(lines)
        else:
            count = range_count(lines, row['line_ranges'])
            if row.get('sha256') and hashlib.sha256(data).hexdigest() != row['sha256']:
                changed_mixed.append(path)
        categories[category] += count
        if path in CALL_SPEC_MODULES:
            continue
        if category in PROOF_CATEGORIES and path.endswith('.v'):
            block_support[category] += count
        elif category == 'block_proofs' and '/Proofs/DecodeItem/' in path and path not in block_paths:
            block_support['proof_helpers'] += count
        elif category == 'composition' and path.endswith('.v'):
            composition_lines += count
    call_spec = []
    for path in sorted(commit.paths):
        if path in CALL_SPEC_MODULES:
            data = commit.read(path)
            dependencies = sorted(require_modules(data.decode()))
            for module in dependencies:
                if module.startswith('ZesuSsz.') and module.replace('.', '/') + '.v' not in commit.paths:
                    raise ValueError('A call-spec dependency is absent: ' + module)
            call_spec.append(dict(path=path, role=CALL_SPEC_MODULES[path], lines=len(data.splitlines()),
                                  requires_before_first_proof=dependencies))
            continue
        if path in listed or not path.endswith('.v') or not re.search(r'decode_?item', path, re.I):
            continue
        raise ValueError('The function-text manifest omits a module: ' + path)
    automation = {path: len(commit.read(path).splitlines()) for path in sorted(commit.paths)
                  if path.startswith('ZesuSsz/Automation/') and path.endswith('.v')}
    return dict(commit=commit.sha,
        counting_rules={'hand': 'Nonblank boundary body lines, excluding native automation lines and Proof/Qed.',
                                'split_blocks': 'An umbrella plus Literal and ShortString modules count as one PC. Both branches must use automation alone for native status. Sum hand lines across non-native branches.',
                                'kinds': KIND_LABEL,
                                'function_text': 'Current whole-file lines; union of manifest ranges in mixed files.',
                                'm2': 'Hand suffix lines plus block support. Composition, tests, call-spec capability, and automation are separate.',
                                'block_support': 'Rocq files in contracts, introductions, exit_meanings, loop_steps, registrations; non-block proof helpers. Composition and call-spec modules are separate.',
                                'composition': 'Composition consumes block proofs and is reported separately from scored M2.',
                                'call_spec_capability': 'The six explicitly reviewed call/compositional modules, counted once whether listed or unlisted. Each row retains its role and explicit imports.',
                                'tests_and_exports': 'All manifest text in tests_and_exports, separate from M2.',
                                'automation': 'Physical lines, including comments and blank lines.'},
                classifier_provenance={'checkpoint': HAND_CHECKPOINT, 'historical_commit': checkpoint['audit_commit'],
                                       'original_classifier_available': False, 'priority': list(KINDS),
                                       'label': KIND_LABEL, 'tokens': TOKENS,
                                       'structural_rule': 'Inherit the next direct line; at proof end inherit the previous direct line.'},
                blocks={'total': len(blocks), 'native': sum(row['status'] == 'native' for row in blocks),
                        'hand': sum(row['status'] == 'hand' for row in blocks), 'rows': blocks},
                hand_suffix_lines=hand_lines, hand_suffix_kinds=dict(kind_totals),
                mixed_lines=mixed_total, structural_lines=structural_total, kind_counts_label=KIND_LABEL,
                function_text_categories={key: categories[key] for key in TEXT_CATEGORIES},
                block_support_categories={key: block_support[key] for key in (*sorted(PROOF_CATEGORIES), 'proof_helpers')},
                block_support_lines=sum(block_support.values()),
                composition_lines=composition_lines,
                call_spec_capability=call_spec,
                call_spec_capability_lines=sum(row['lines'] for row in call_spec),
                tests_and_exports_lines=categories['tests_and_exports'],
                m2_total_lines=hand_lines + sum(block_support.values()),
                automation_lines=sum(automation.values()), automation_files=len(automation),
                changed_mixed_manifest_files=changed_mixed)


TEXT_KINDS = ('hand_written', 'generated', 'data_table')


def manifest_path(commit, function):
    matches = []
    for path in sorted(commit.paths):
        if path.startswith('ZesuSsz/Evidence/') and path.endswith('_function_text.json'):
            data = json.loads(commit.read(path))
            name = data.get('function')
            if name == function or (isinstance(name, str) and name.rsplit('.', 1)[-1] == function):
                matches.append((path, data))
    if len(matches) != 1:
        raise ValueError('The counter needs one function manifest: ' + function)
    return matches[0]


def selected_indices(lines, row):
    if row['scope'] == 'whole_file':
        return set(range(len(lines)))
    if row['scope'] != 'mixed_file':
        raise ValueError('The manifest has an unknown scope: ' + row['path'])
    indices = set()
    if not isinstance(row.get('line_ranges'), list):
        raise ValueError('A mixed-file row needs line_ranges.')
    for bounds in row['line_ranges']:
        if (not isinstance(bounds, list) or len(bounds) != 2 or
                any(type(value) is not int for value in bounds)):
            raise ValueError('A manifest range needs two integer bounds.')
        first, last = bounds
        if not 1 <= first <= last <= len(lines):
            raise ValueError('A manifest range is outside its file.')
        current = set(range(first - 1, last))
        if indices & current:
            raise ValueError('The manifest overlaps a selected line: ' + row['path'])
        indices.update(current)
    return indices


def freshness_binding(commit, manifest, generator, receipt):
    """Accept generated credit only for an exact successful check on this tree."""
    generators = manifest.get('generators', {})
    if not isinstance(generators, dict):
        raise ValueError('Manifest generators must be an object.')
    specification = generators.get(generator)
    if not isinstance(specification, dict):
        raise ValueError('A generated row needs a declared generator: ' + str(generator))
    command = specification.get('command')
    if not isinstance(command, list) or '--check' not in command or any(not isinstance(x, str) for x in command):
        raise ValueError('A generator needs an explicit --check command.')
    inputs, outputs = specification.get('inputs'), specification.get('outputs')
    for paths in (inputs, outputs):
        if not isinstance(paths, list) or not paths or any(not isinstance(x, str) for x in paths) or len(paths) != len(set(paths)):
            raise ValueError('A generator needs explicit unique input and output lists.')
    if not isinstance(specification.get('tool'), str) or specification['tool'] not in inputs:
        raise ValueError('The generator tool must be an explicit input.')
    if receipt is None:
        return None
    tree = commit.git('rev-parse', commit.sha + '^{tree}').strip()
    if not isinstance(receipt, dict) or receipt.get('schema_version') != 1 or receipt.get('tree') != tree:
        raise ValueError('The freshness record does not bind this source tree.')
    if not isinstance(receipt.get('checks'), dict):
        raise ValueError('The freshness checks must be an object.')
    checked = receipt['checks'].get(generator)
    if not isinstance(checked, dict) or type(checked.get('exit_code')) is not int or checked['exit_code'] != 0:
        raise ValueError('The generator has no successful freshness check: ' + generator)
    if checked.get('command') != command:
        raise ValueError('The freshness command differs from its manifest.')
    for label, paths in (('inputs', inputs), ('outputs', outputs)):
        expected = {path: hashlib.sha256(commit.read(path)).hexdigest() for path in paths}
        if checked.get(label) != expected:
            raise ValueError('The freshness ' + label + ' differ from this source tree.')
    return checked


def count_schema2(commit, path, manifest, freshness=None):
    if not isinstance(manifest.get('scope_id'), str) or not manifest['scope_id'].strip():
        raise ValueError('A schema-2 manifest needs an explicit scope_id.')
    if not isinstance(manifest.get('inventory_only', False), bool):
        raise ValueError('The inventory_only flag must be boolean.')
    groups = {category: {kind: dict(physical=0, nonblank=0) for kind in TEXT_KINDS}
              for category in TEXT_CATEGORIES}
    support = {kind: dict(physical=0, nonblank=0) for kind in TEXT_KINDS}
    selected, rows, checks = {}, [], {}
    function = manifest['function']
    is_decode_item = function.rsplit('.', 1)[-1] == 'decodeItem'
    blocks, block_paths = [], set()
    if is_decode_item:
        with tempfile.TemporaryDirectory(prefix='lithium-metrics-') as directory:
            blocks, block_paths = block_counts(commit, directory)
        if len(blocks) != 24:
            raise ValueError('The commit must contain exactly 24 distinct blocks.')
    if not isinstance(manifest.get('files'), list):
        raise ValueError('The manifest files must be a list.')
    for row in manifest['files']:
        if not isinstance(row, dict) or not isinstance(row.get('path'), str) or not isinstance(row.get('category'), str):
            raise ValueError('Each manifest row needs a path and category.')
        source, category, kind = row['path'], row['category'], row.get('text_kind')
        relative = Path(source)
        if relative.is_absolute() or '..' in relative.parts or not source or source not in commit.paths:
            raise ValueError('The manifest path leaves the source tree: ' + source)
        if category not in groups or kind not in TEXT_KINDS:
            raise ValueError('The manifest needs an explicit category and text_kind: ' + source)
        data = commit.read(source)
        lines = data.splitlines()
        indices = selected_indices(lines, row)
        if selected.setdefault(source, set()) & indices:
            raise ValueError('The manifest overlaps a selected line: ' + source)
        selected[source].update(indices)
        effective, status = kind, 'not_required'
        if kind == 'generated':
            generator = row.get('generator')
            if not isinstance(generator, str) or not generator:
                raise ValueError('A generated row needs a named generator: ' + source)
            if generator not in checks:
                checks[generator] = freshness_binding(commit, manifest, generator, freshness)
            if source not in manifest['generators'][generator]['outputs']:
                raise ValueError('The generated source is absent from its output list: ' + source)
            status = 'passed' if checks[generator] is not None else 'unchecked'
            if status != 'passed':
                effective = 'hand_written'
        counts = dict(physical=len(indices), nonblank=sum(bool(lines[i].strip()) for i in indices))
        for unit, count in counts.items():
            groups[category][effective][unit] += count
        contributes = (source not in CALL_SPEC_MODULES and
                       ((category in PROOF_CATEGORIES and source.endswith('.v')) or
                        (category == 'block_proofs' and source not in block_paths and
                         source.startswith('ZesuSsz/Proofs/' + function.rsplit('.', 1)[-1][:1].upper() + function.rsplit('.', 1)[-1][1:] + '/'))))
        if contributes:
            for unit, count in counts.items():
                support[effective][unit] += count
        rows.append(dict(path=source, category=category, text_kind=kind, effective_text_kind=effective,
                         freshness=status, sha256=hashlib.sha256(data).hexdigest(),
                         scope=row['scope'], line_ranges=row.get('line_ranges'), counts=counts,
                         block_support=contributes))
    if is_decode_item:
        for source in commit.paths:
            if source.endswith('.v') and re.search(r'decode_?item', source, re.I) and source not in selected and source not in CALL_SPEC_MODULES:
                raise ValueError('The function-text manifest omits a module: ' + source)
    automation = {source: commit.read(source).splitlines() for source in sorted(commit.paths)
                  if source.startswith('ZesuSsz/Automation/') and source.endswith('.v')}
    hand = sum(row['lines'] for row in blocks)
    categories = {category: sum(cell['physical'] for cell in kinds.values()) for category, kinds in groups.items()}
    call_spec = []
    for source, role in sorted(CALL_SPEC_MODULES.items()):
        if not is_decode_item or source not in commit.paths:
            continue
        data = commit.read(source)
        dependencies = sorted(require_modules(data.decode()))
        for module in dependencies:
            if module.startswith('ZesuSsz.') and module.replace('.', '/') + '.v' not in commit.paths:
                raise ValueError('A call-spec dependency is absent: ' + module)
        call_spec.append(dict(path=source, role=role, lines=len(data.splitlines()),
                              nonblank_lines=sum(bool(line.strip()) for line in data.splitlines()),
                              requires_before_first_proof=dependencies))
    return dict(commit=commit.sha, schema_version=2, function=function,
                tree=commit.git('rev-parse', commit.sha + '^{tree}').strip(),
                scope_id=manifest['scope_id'], manifest=dict(path=path, sha256=hashlib.sha256(commit.read(path)).hexdigest()),
                inventory_only=manifest.get('inventory_only', False),
                counting_rules={'text_kind': 'Explicit manifest metadata only. Unchecked generated text counts as hand-written.',
                                'units': 'Physical lines include blank lines. Nonblank lines exclude whitespace-only lines.',
                                'overlap': 'Reject repeated selected lines within this function.',
                                'm2_total_lines': 'Mixed compatibility unit: nonblank hand suffix lines plus physical hand-written support lines.',
                                'm2_nonblank_lines': 'Uniform headline: nonblank hand suffix lines plus nonblank hand-written support lines. Generated and data-table support stay separate.',
                                'attribution': 'Per-function totals include explicitly shared ranges. Their sum is not a unique project total.'},
                blocks=dict(total=len(blocks), native=sum(row['status'] == 'native' for row in blocks),
                            hand=sum(row['status'] == 'hand' for row in blocks), rows=blocks,
                            coverage='committed boundary bodies' if is_decode_item else 'not_measured'),
                hand_suffix_lines=hand, hand_suffix_unit='nonblank',
                function_text_categories=categories, function_text_by_kind=groups, files=rows,
                block_support_by_kind=support, block_support_lines=sum(cell['physical'] for cell in support.values()),
                hand_written_support_lines=support['hand_written']['nonblank'],
                m2_total_lines=hand + support['hand_written']['physical'],
                m2_nonblank_lines=hand + support['hand_written']['nonblank'],
                composition_lines=categories['composition'], tests_and_exports_lines=categories['tests_and_exports'],
                call_spec_capability=call_spec, call_spec_capability_lines=sum(row['lines'] for row in call_spec),
                automation_lines=sum(len(lines) for lines in automation.values()),
                automation_nonblank_lines=sum(bool(line.strip()) for lines in automation.values() for line in lines),
                automation_files=len(automation),
                freshness_record_hash_format='SHA256 of JSON with sorted keys and default separators',
                freshness_record_sha256=(hashlib.sha256(json.dumps(freshness, sort_keys=True).encode()).hexdigest() if freshness is not None else None))


def count_commit(commit, function='decodeItem', freshness=None):
    path, manifest = manifest_path(commit, function)
    if manifest.get('schema_version') == 1:
        if path != MANIFEST:
            raise ValueError('Schema-1 historical counting supports decodeItem only.')
        report = count_legacy_commit(commit)
        report.update(schema_version=1, scope_id='decodeItem-legacy-schema-1', function=manifest['function'])
        return report
    if manifest.get('schema_version') != 2:
        raise ValueError('The counter supports manifest schema 1 or 2.')
    return count_schema2(commit, path, manifest, freshness)


def comparison_table(before, after):
    if before.get('scope_id') != after.get('scope_id'):
        return ('Noncomparable scopes: ' + str(before.get('scope_id')) + ' versus ' +
                str(after.get('scope_id')) + '. No delta is reported.')
    if before.get('schema_version') == 2:
        rows = []
        for category in TEXT_CATEGORIES:
            for kind in TEXT_KINDS:
                for unit in ('physical', 'nonblank'):
                    rows.append((category + '/' + kind + '/' + unit,
                                 before['function_text_by_kind'][category][kind][unit],
                                 after['function_text_by_kind'][category][kind][unit]))
        table = ['| Category/kind/unit | Before | After | Delta |', '|---|---:|---:|---:|']
        return '\n'.join(table + [f'| {label} | {old} | {new} | {new - old:+d} |' for label, old, new in rows])
    rows = [('Native blocks', before['blocks']['native'], after['blocks']['native']),
            ('Hand blocks', before['blocks']['hand'], after['blocks']['hand']),
            ('Hand suffix lines', before['hand_suffix_lines'], after['hand_suffix_lines'])]
    for category in before['block_support_categories']:
        rows.append((category, before['block_support_categories'][category], after['block_support_categories'][category]))
    for label, key in [('Block support total', 'block_support_lines'), ('M2 total', 'm2_total_lines'),
                       ('Composition', 'composition_lines'),
                       ('Tests and exports', 'tests_and_exports_lines'),
                       ('Call-spec capability', 'call_spec_capability_lines'), ('Automation', 'automation_lines')]:
        rows.append((label, before[key], after[key]))
    table = [f"| Category | {before['commit'][:8]} | {after['commit'][:8]} | Delta |",
             '|---|---:|---:|---:|']
    table.extend(f'| {label} | {old} | {new} | {new - old:+d} |' for label, old, new in rows)
    return '\n'.join(table)


def main(argv=None):
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', default='HEAD')
    parser.add_argument('--compare', help='Print a category table against this baseline commit.')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--function', default='decodeItem')
    parser.add_argument('--freshness', type=Path, help='Exact successful generator checks for this tree.')
    args = parser.parse_args(argv)
    try:
        freshness = json.loads(args.freshness.read_text()) if args.freshness else None
        def measure(revision):
            commit = Commit(root, revision)
            if args.function == 'all':
                functions = [json.loads(commit.read(path))['function'] for path in sorted(commit.paths)
                             if path.startswith('ZesuSsz/Evidence/') and path.endswith('_function_text.json')]
                reports = {function: count_commit(commit, function, freshness) for function in functions}
                attribution = {}
                for function, result in reports.items():
                    for row in result.get('files', []):
                        attribution.setdefault(row['path'], []).append(function)
                return dict(commit=commit.sha, functions=reports, shared_attribution={path: sorted(set(names)) for path, names in attribution.items() if len(set(names)) > 1})
            return count_commit(commit) if args.function == 'decodeItem' and freshness is None else count_commit(commit, args.function, freshness)
        report = measure(args.commit)
        before = measure(args.compare) if args.compare else None
        if args.function == 'all' and args.compare:
            raise ValueError('--compare requires one explicit function.')
        common = Path(subprocess.check_output(['git', '-C', str(root), 'rev-parse', '--path-format=absolute', '--git-common-dir'], text=True).strip())
        output = args.output or common.parent / 'docs/ai/metrics/lithium_idioms.json'
        document = json.loads(output.read_text()) if output.exists() else {'schema_version': 1}
        if not isinstance(document, dict) or not isinstance(document.get('m2_by_commit', {}), dict):
            raise ValueError('The metrics document must contain an object of M2 counts.')
        if args.function == 'decodeItem':
            measurements = document.setdefault('m2_by_commit', {})
            if before:
                measurements[before['commit']] = before
            measurements[report['commit']] = report
        else:
            measurements = document.setdefault('function_text_by_commit', {})
            if not isinstance(measurements, dict):
                raise ValueError('The function metrics must be an object.')
            for result in ([before, report] if before else [report]):
                functions = result['functions'] if args.function == 'all' else {result['function']: result}
                existing = measurements.setdefault(result['commit'], {})
                if not isinstance(existing, dict):
                    raise ValueError('The commit function metrics must be an object.')
                existing.update(functions)
                if args.function == 'all':
                    document.setdefault('shared_function_attribution_by_commit', {})[result['commit']] = result['shared_attribution']
        output.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(mode='w', dir=output.parent, prefix=output.name + '.', delete=False) as temporary:
            temporary.write(json.dumps(document, indent=2) + '\n')
            pending = Path(temporary.name)
        try:
            pending.replace(output)
        finally:
            pending.unlink(missing_ok=True)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.error(str(error))
    print(comparison_table(before, report) if before else json.dumps(report, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
