#!/usr/bin/env python3
"""Count decodeItem source text at a commit without running a proof."""

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
PROOF_CATEGORIES = {'contracts', 'introductions', 'exit_meanings', 'loop_steps', 'registrations', 'composition'}



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


def count_commit(commit):
    manifest = json.loads(commit.read(MANIFEST))
    checkpoint = json.loads(commit.read(HAND_CHECKPOINT))
    blocks = []
    hand_lines = 0
    kind_totals = Counter()
    mixed_total = structural_total = 0
    with tempfile.TemporaryDirectory(prefix='lithium-metrics-') as directory:
        for path in sorted(commit.paths):
            if not re.fullmatch(r'ZesuSsz/Proofs/DecodeItem/(?:Hand|Auto)/Block[0-9a-fA-F]+\.v', path):
                continue
            text = commit.read(path).decode()
            temporary = Path(directory) / Path(path).name
            temporary.write_text(text)
            proofs = [proof for proof in parse_module(temporary) if proof.name.startswith('DesignedBoundary_')]
            if len(proofs) != 1:
                raise ValueError('The block must contain one boundary theorem: ' + path)
            proof = proofs[0]
            native = proof.automation_only
            count = 0 if native else len(proof.hand_lines)
            hand_lines += count
            kinds, mixed, structural = classify_lines(proof.hand_lines) if not native else (dict.fromkeys((*KINDS, 'other'), 0), 0, 0)
            kind_totals.update(kinds)
            mixed_total += mixed
            structural_total += structural
            blocks.append(dict(pc=Path(path).stem.removeprefix('Block'), path=path,
                               status='native' if native else 'hand', lines=count, kinds=kinds, mixed_lines=mixed, structural_lines=structural))
    if len({row['pc'] for row in blocks}) != len(blocks) or len(blocks) != 24:
        raise ValueError('The commit must contain exactly 24 distinct blocks.')
    categories = Counter()
    other_proof_text = 0
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
        if category in PROOF_CATEGORIES and path.endswith('.v'):
            other_proof_text += count
        elif category == 'block_proofs' and '/Proofs/DecodeItem/' in path and not re.search(r'/Block[0-9a-fA-F]+\.v$', path):
            other_proof_text += count
    call_glue = []
    for path in sorted(commit.paths):
        if path in listed or not path.endswith('.v') or not re.search(r'decode_?item', path, re.I):
            continue
        if not re.search(r'/(?:Contracts|Compliance)/DecodeItem(?:Call|Compositional)[^/]*\.v$', path):
            raise ValueError('The function-text manifest omits a module: ' + path)
        count = len(commit.read(path).splitlines())
        call_glue.append(dict(path=path, lines=count))
        other_proof_text += count
    automation = {path: len(commit.read(path).splitlines()) for path in sorted(commit.paths)
                  if path.startswith('ZesuSsz/Automation/') and path.endswith('.v')}
    return dict(commit=commit.sha,
                counting_rules={'hand': 'Nonblank boundary body lines, excluding native automation lines and Proof/Qed.',
                                'kinds': KIND_LABEL,
                                'function_text': 'Current whole-file lines; union of manifest ranges in mixed files.',
                                'other_proof_text': 'Rocq files in contracts, introductions, exit_meanings, loop_steps, registrations, composition; non-block proof helpers; unlisted call-spec glue.',
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
                call_spec_glue=call_glue, other_proof_text_lines=other_proof_text,
                m2_total_lines=hand_lines + other_proof_text,
                automation_lines=sum(automation.values()), automation_files=len(automation),
                changed_mixed_manifest_files=changed_mixed)


def main(argv=None):
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', default='HEAD')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    try:
        report = count_commit(Commit(root, args.commit))
        common = Path(subprocess.check_output(['git', '-C', str(root), 'rev-parse', '--path-format=absolute', '--git-common-dir'], text=True).strip())
        output = args.output or common.parent / 'docs/ai/metrics/lithium_idioms.json'
        document = json.loads(output.read_text()) if output.exists() else {'schema_version': 1}
        if not isinstance(document, dict) or not isinstance(document.get('m2_by_commit', {}), dict):
            raise ValueError('The metrics document must contain an object of M2 counts.')
        document.setdefault('m2_by_commit', {})[report['commit']] = report
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
    print(json.dumps(report, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
