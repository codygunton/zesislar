#!/usr/bin/env python3
"""Classify block-run records and print a wave summary + CSV."""
import csv, json, re, statistics, sys
from pathlib import Path

DIS = {}
# Entry states that carry their own handoff inside the block (static scan of the spec text):
# the run closes at that handoff, not at the block exit.
INSTATE = {'0x15930': 0x1593c, '0x15940': 0x1594c, '0x15950': 0x1595c, '0x15960': 0x15968, '0x14d80': 0x14e00}
LOADS = {'ld', 'lw', 'lwu', 'lh', 'lhu', 'lb', 'lbu'}
CLASS_KIND = {'C3': 'sealed bundle', 'C4': 'pure'}


def final_goal(out):
    """The last Show (after shelving term goals): the Prop residual."""
    tail = out.split('BOUNDARY-ALL-GOALS-END')[-1]
    parts = re.split(r'-{10,}∗\n', tail)
    if len(parts) < 2:
        return tail, ''
    return tail, re.split(r'\n(?=\S)', parts[-1])[0].strip()


def classify(r):
    out = Path(r['raw_path']).read_text() if r.get('raw_path') else ''
    lo = int(r['leader'], 16)
    pcs = [int(x) for x in re.findall(r'BLK-PC \(bv_to_bvn \(Z_to_bv 64 (\d+)\)\)', out)] if out else []
    inblk = [x for x in pcs if lo <= x <= int(r['last'], 16)]
    k = (max(inblk) - lo) // 4 + 1 if inblk else 1
    o = r.get('outcome')
    res = dict(result=o, k=k)
    if (o == 'closed-all' and r['leader'] in INSTATE
            and not r.get('interior_handoffs_stripped')):
        h = INSTATE[r['leader']]
        res.update(result='partial', k=(h - lo) // 4, stall_pc=hex(h), stall_insn=' '.join(DIS.get(h, ('?', ''))),
                   stall_kind='in-state handoff')
        return res
    if o == 'closed-all':
        res.update(result='closed', k=r['n'])
    elif o == 'probe':
        tail, concl = final_goal(out)
        if re.fullmatch(r'BLK_STOP_[0-9a-f]+', concl):
            res.update(result='reached', k=r['n'])
        else:
            res.update(result='stalled', cls=r.get('pred_class') or '?',
                       concl1=(concl.split('\n')[0] if concl else (r.get('conclusion') or '').strip().split('\n')[0])[:160])
    elif o in ('timeout', 'memory'):
        res.update(result=o)
    if res['result'] in ('stalled', 'timeout', 'memory'):
        pc = lo + 4 * (k - 1)
        m, ops = DIS.get(pc, ('?', ''))
        nxt = DIS.get(pc + 4, ('', ''))[0]
        if m in ('jal', 'jalr') or (m == 'auipc' and nxt == 'jalr'):
            kind = 'call'
        elif m in LOADS:
            kind = 'load'
        elif res.get('cls') in CLASS_KIND:
            kind = CLASS_KIND[res['cls']]
        else:
            kind = 'other'
        res.update(stall_pc=hex(pc), stall_insn=f'{m} {ops}'.strip(), stall_kind=kind)
    return res


def write_table(records, blocks, destination):
    global DIS
    DIS = {insn["pc"]: (insn["mnemonic"], insn["operands"])
           for block in blocks for insn in block["instructions"]}
    rows = []
    for record in records:
        row = dict(run=record.get("run", "A"), variant=record["variant"],
                   leader=record["leader"], n=record["n"], kind=record["kind"],
                   lemma=record.get("lemma"), cap=record.get("cap"), wall_s=record.get("seconds"),
                   cpu_s=record.get("cpu"), peak_mib=record.get("peak_mib"),
                   stops=" ".join(record.get("stops", [])), kept=" ".join(record.get("kept_succ", [])))
        row.update(dict(result="no-entry") if record["outcome"] == "skipped-no-entry" else classify(record))
        rows.append(row)
    rows.sort(key=lambda row: int(row["leader"], 16))
    keys = ["run", "variant", "leader", "n", "kind", "lemma", "result", "k", "cls", "stall_pc", "stall_insn",
            "stall_kind", "concl1", "wall_s", "cpu_s", "peak_mib", "cap", "stops", "kept"]
    with destination.open("w", newline="") as output:
        writer = csv.DictWriter(output, keys, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    return rows


def compare_table(actual, expected):
    """Return outcome differences, including absent or added leaders."""
    def read(path):
        with path.open(newline="") as source:
            return {row["leader"]: row["result"] for row in csv.DictReader(source)}
    observed, baseline = read(actual), read(expected)
    return [{"leader": leader, "expected": baseline.get(leader), "actual": observed.get(leader)}
            for leader in sorted(observed.keys() | baseline.keys(), key=lambda value: int(value, 16))
            if observed.get(leader) != baseline.get(leader)]
