#!/usr/bin/env python3
"""Triage the open blocks of a BENCH run: one markdown row per open block with its class, owner and
next action.

usage: triage.py RUN_DIR [--render RENDER_DIR ...] [--classes PATH] [--json]

Reads the run through bench_report.load_run. Each leftover of a block gets a head (see "about" in
triage_classes.json) and the first class of triage_classes.json that matches it; a block whose run
ended at a cap or was killed gets the class whose "ends" names that end (OVER, KILLED). A block's
class is the first one in table order among its leftovers; UNCLASSIFIED (no class matched) prints
the head instead. Blocks of the set that have no result yet are listed after the table.

--render names render_function.sh run directories (render/RESULT.json, callers/CALLERS.json): every
caller the render refused gets a row too, REFUSED/<refusal kind> when its own entry was refused
(the kinds and details of the render's refusal reports) and BLOCKED when only a successor entry or
the function-return package was not rendered. The last line counts the blocks per class, closed
ones included, so one command gives a held-out report.
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
    end = block['end']
    over = next((entry['id'] for entry in classes
                 if end in entry.get('ends', ()) or end.split(' ', 1)[0] in entry.get('ends', ())), None)
    labelled = [(classify(head, size, classes), head) for head, size in leftover_heads(block)]
    counts = Counter(label for label, _ in labelled)
    if over:
        return {'class': over, 'leftovers': counts, 'head': labelled[0][1] if labelled else ''}
    if not labelled:
        return {'class': UNCLASSIFIED, 'leftovers': counts, 'head': 'no leftover, run end ' + block['end']}
    label, head = min(labelled, key=lambda item: by_id.get(item[0], len(classes)))
    return {'class': label, 'leftovers': counts, 'head': head}


STEP_OUTPUTS = (('loop-heads', 'loop-heads.json'), ('render', 'render/RESULT.json'), ('callers', 'callers/CALLERS.json'))


def pc_key(pc):
    """A render case's pc as an integer, or its name (`function_return_022c`)."""
    return int(pc, 16) if re.fullmatch(r'0x[0-9a-fA-F]+', pc) else pc


def stopped_render_rows(directory):
    """Rows for a render that stopped before its entries (no render/RESULT.json): every forward
    boundary is REFUSED/<step>-stopped, the head being the last line of that step's log."""
    forward = json.loads((directory / 'forward' / 'RESULT.json').read_text())
    step = next((name for name, output in STEP_OUTPUTS if not (directory / output).exists()), 'forward')
    log = directory / (step + '.log')
    lines = [line.strip() for line in log.read_text(errors='replace').splitlines() if line.strip()] \
        if log.is_file() else []
    head = lines[-1] if lines else 'no %s output' % step
    boundaries = [int(row['pc'], 16) for row in forward.get('boundaries', [])]
    entry = boundaries[0] if boundaries else 0
    return [{'class': 'REFUSED/%s-stopped' % step, 'key': '%s/%04x' % (forward.get('function', directory.name),
                                                                      pc - entry),
             'end': 'render', 'cpu': None, 'leftovers': Counter(), 'head': head} for pc in boundaries]


def render_rows(directory):
    """Rows of the callers a render refused: REFUSED/<kind> (own entry) or BLOCKED (a successor
    entry or the return package not rendered), each with the render's refusal detail as head."""
    directory = Path(directory)
    if not (directory / 'render' / 'RESULT.json').is_file():
        return stopped_render_rows(directory)
    result = json.loads((directory / 'render' / 'RESULT.json').read_text())
    callers = json.loads((directory / 'callers' / 'CALLERS.json').read_text())
    reports = {pc_key(case['pc']): case.get('reports') or [] for case in result.get('cases', [])
               if case.get('status') != 'source_declarations_rendered'}
    stops = [report for case_reports in reports.values() for report in case_reports
             if report.get('kind', '').endswith('_stop')]

    def kinds(pc):
        found = reports.get(pc, [])
        return ('/'.join(sorted({report.get('kind', '?') for report in found})) or 'unknown',
                found[0].get('detail', '') if found else '')

    pcs = {row['case']: pc_key(row['pc']) for row in callers['rows']}
    rows = []
    for row in callers['rows']:
        if row['status'] != 'refused':
            continue
        key = '%s/%s' % (callers.get('function', directory.name), row['case'])
        reason = row.get('reason', '')
        if reason == 'own entry not rendered':
            kind, detail = kinds(pcs[row['case']])
            rows.append({'class': 'REFUSED/' + kind, 'key': key, 'end': 'render', 'cpu': None,
                         'leftovers': Counter(), 'head': detail})
            continue
        match = re.match(r'successor entry not rendered: (\S+)', reason)
        package = reason.startswith('function-return package')
        if match and match[1] in pcs:
            kind, detail = kinds(pcs[match[1]])
            head = '%s (%s: %s)' % (reason, kind, detail)
        elif package and stops:
            head = '%s (%s: %s)' % (reason, stops[0].get('kind'), stops[0].get('detail', ''))
        else:
            head = reason
        rows.append({'class': 'BLOCKED' if match or package else 'REFUSED/' + (reason or 'unknown'),
                     'key': key, 'end': 'render', 'cpu': None, 'leftovers': Counter(), 'head': head})
    return rows


def triage(run, classes, renders=()):
    rows, pending, closed = [], [], 0
    for entry in run['blocks']:
        block = entry['block']
        if entry['row'] is None or block is None:
            pending.append(entry['key'])
            continue
        if block['verdict'] == 'CLOSED':
            closed += 1
            continue
        rows.append(dict(triage_block(block, classes), key=entry['key'], end=block['end'], cpu=block['cpu']))
    for directory in renders:
        rows.extend(render_rows(directory))
    return rows, pending, closed


def summary(rows, closed):
    counts = Counter(row['class'].split('/', 1)[0] for row in rows)
    total = closed + sum(counts.values())
    return '%d blocks: CLOSED %d; %s' % (total, closed, ', '.join('%s %d' % item for item in sorted(counts.items())))


def cell(text, limit=120):
    text = text if len(text) <= limit else text[:limit - 1] + '…'
    return text.replace('|', '\\|')


def render(rows, pending, classes, closed=0):
    info = {entry['id']: entry for entry in classes}
    lines = ['| block | end | CPU-s | class | owner | next action | leftovers | head |',
             '|---|---|---|---|---|---|---|---|']
    for row in rows:
        entry = info.get(row['class'], info.get(row['class'].split('/', 1)[0], {}))
        leftovers = ', '.join('%s x%d' % item for item in sorted(row['leftovers'].items()))
        lines.append('| %s | %s | %s | %s | %s | %s | %s | `%s` |' % (
            row['key'], row['end'], R.number(row['cpu']), row['class'], entry.get('owner', '-'),
            entry.get('next_action', 'read the head; add a class to triage_classes.json'), leftovers or '-',
            cell(row['head'])))
    if pending:
        lines.append('')
        lines.append('no result yet: ' + ', '.join(pending))
    lines.append('')
    lines.append(summary(rows, closed))
    return '\n'.join(lines) + '\n'


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('run', type=Path)
    parser.add_argument('--classes', type=Path, default=BENCH / 'triage_classes.json')
    parser.add_argument('--render', type=Path, action='append', default=[],
                        help='a render_function.sh run directory whose refused callers get rows (repeatable)')
    parser.add_argument('--json', action='store_true')
    options = parser.parse_args(argv)
    classes = load_classes(options.classes)
    rows, pending, closed = triage(R.load_run(options.run), classes, options.render)
    if options.json:
        print(json.dumps({'open': rows, 'no_result': pending, 'closed': closed,
                          'summary': summary(rows, closed)}, indent=1))
    else:
        print(render(rows, pending, classes, closed), end='')
    return 0


if __name__ == '__main__':
    sys.exit(main())
