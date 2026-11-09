#!/usr/bin/env python3
"""Parse a stamped `Print Ltac` probe log into {fullname: body} and list solver users."""
import re, sys, json
from pathlib import Path

def parse(log):
    out, cur, buf = {}, None, []
    for raw in Path(log).read_text().splitlines():
        line = raw.split(' ', 1)[1] if ' ' in raw else ''
        m = re.match(r'Ltac (\S+)( .*)? :=$', line) or re.match(r'Ltac (\S+)( .*)? :=\s*(.*)$', line)
        if m and not line.startswith(' '):
            if cur: out[cur] = '\n'.join(buf)
            cur, buf = m.group(1), [line]
            continue
        if cur is not None:
            if line.startswith(' ') or line.startswith('Redefined') or re.match(r'^[A-Z][\w.]*$', line):
                buf.append(line)
            else:
                out[cur] = '\n'.join(buf); cur = None
    if cur: out[cur] = '\n'.join(buf)
    return out

TOK = re.compile(r"(?<![\w.])((?:[\w]+\.)*(?:lia|nia|bv_solve|xlia|xnia|zesu_solve_machine_linear|zesu_solve_machine_bounds|zesu_finish_lia|zesu_solve_selected|zesu_lia_linear_first3))(?![\w'])")
if __name__ == '__main__':
    bodies = parse(sys.argv[1])
    users = {}
    for name, body in bodies.items():
        toks = sorted(set(TOK.findall(body.split(':=', 1)[1] if ':=' in body else body)))
        if toks: users[name] = toks
    json.dump({'bodies': bodies, 'users': users}, open(sys.argv[2], 'w'), indent=1)
    print(len(bodies), 'bodies;', len(users), 'solver users')
    from collections import Counter
    c = Counter(n.rsplit('.', 1)[0] for n in users)
    for k, v in c.most_common(): print(v, k)
