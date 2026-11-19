#!/usr/bin/env python3
"""Triage the open blocks of a BENCH run: one markdown row per open block with its class, owner and
next action.

usage: triage.py RUN_DIR [--classes PATH] [--json]

Reads the run through bench_report.load_run. Each leftover of a block gets a head (see "about" in
triage_classes.json) and the first class of triage_classes.json that matches it; a block whose run
ended at a cap is OVER. A block's class is the first one in table order among its leftovers;
UNCLASSIFIED (no class matched) prints the head instead. Blocks of the set that have no result yet
are listed after the table.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

BENCH = Path(__file__).resolve().parent
sys.path.insert(0, str(BENCH))
import bench_report as R  # noqa: E402

UNCLASSIFIED = 'UNCLASSIFIED'
CALLEE_PREMISE = re.compile(r'instr_pre\s+\S+\s+\((?!ZesuSsz\.Generated\.)')


def load_classes(path=BENCH / 'triage_classes.json'):
    classes = json.loads(Path(path).read_text())['classes']
    for entry in classes:
        if 'regex' in entry:
            entry['pattern'] = re.compile(entry['regex'], re.S)
    return classes


def calls_out(block):
    """Whether the block's caller has a callee spec among its premises."""
    callers = list(Path(block['dir']).glob('Caller*.v'))
    return bool(callers) and bool(CALLEE_PREMISE.search(callers[0].read_text()))


def leftover_heads(block):
    """(head, statement bytes or None) per leftover of a block that did not close."""
    heads = []
    for leftover in block['leftovers']:
        if leftover.get('statement'):
            conclusion = ' '.join(R.conclusion_of(leftover['statement']).split())
            heads.append(('pure ' + conclusion, len(leftover['statement'].encode())))
        else:
            kind = 'spatial-call' if calls_out(block) else 'spatial'
            heads.append(('%s %s' % (kind, leftover.get('site') or '?'), None))
    if not heads:
        for error in block['errors']:
            first = next((line.strip() for line in error['text'].splitlines()
                          if line.strip() and line.strip() != 'Error:'), 'error')
            heads.append(('error ' + re.sub(r'^\(in proof [^)]*\):\s*', '', first), None))
    return heads


def classify(head, size, classes):
    for entry in classes:
        pattern = entry.get('pattern')
        if pattern is None or not pattern.search(head):
            continue
        if entry.get('max_bytes') is not None and (size is None or size > entry['max_bytes']):
            continue
        return entry['id']
    return UNCLASSIFIED


def triage_block(block, classes):
    """{class, leftovers: Counter of classes, head} of one open block."""
    by_id = {entry['id']: index for index, entry in enumerate(classes)}
    over = next((entry['id'] for entry in classes if block['end'] in entry.get('ends', ())), None)
    labelled = [(classify(head, size, classes), head) for head, size in leftover_heads(block)]
    counts = Counter(label for label, _ in labelled)
    if over:
        return {'class': over, 'leftovers': counts, 'head': labelled[0][1] if labelled else ''}
    if not labelled:
        return {'class': UNCLASSIFIED, 'leftovers': counts, 'head': 'no leftover, run end ' + block['end']}
    label, head = min(labelled, key=lambda item: by_id.get(item[0], len(classes)))
    return {'class': label, 'leftovers': counts, 'head': head}


def triage(run, classes):
    rows, pending = [], []
    for entry in run['blocks']:
        block = entry['block']
        if entry['row'] is None or block is None:
            pending.append(entry['key'])
            continue
        if block['verdict'] == 'CLOSED':
            continue
        rows.append(dict(triage_block(block, classes), key=entry['key'], end=block['end'], cpu=block['cpu']))
    return rows, pending


def cell(text, limit=120):
    text = text if len(text) <= limit else text[:limit - 1] + '…'
    return text.replace('|', '\\|')


def render(rows, pending, classes):
    info = {entry['id']: entry for entry in classes}
    lines = ['| block | end | CPU-s | class | owner | next action | leftovers | head |',
             '|---|---|---|---|---|---|---|---|']
    for row in rows:
        entry = info.get(row['class'], {})
        leftovers = ', '.join('%s x%d' % item for item in sorted(row['leftovers'].items()))
        lines.append('| %s | %s | %s | %s | %s | %s | %s | `%s` |' % (
            row['key'], row['end'], R.number(row['cpu']), row['class'], entry.get('owner', '-'),
            entry.get('next_action', 'read the head; add a class to triage_classes.json'), leftovers or '-',
            cell(row['head'])))
    if pending:
        lines.append('')
        lines.append('no result yet: ' + ', '.join(pending))
    return '\n'.join(lines) + '\n'


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('run', type=Path)
    parser.add_argument('--classes', type=Path, default=BENCH / 'triage_classes.json')
    parser.add_argument('--json', action='store_true')
    options = parser.parse_args(argv)
    classes = load_classes(options.classes)
    rows, pending = triage(R.load_run(options.run), classes)
    if options.json:
        print(json.dumps({'open': rows, 'no_result': pending}, indent=1))
    else:
        print(render(rows, pending, classes), end='')
    return 0


if __name__ == '__main__':
    sys.exit(main())
