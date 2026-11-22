"""Loop structure of a function's block CFG: dominator-based natural loops.

A back edge is an edge u -> h whose target h dominates u; h is a loop head and
its natural loop is h with every block that reaches a back-edge source without
passing through h. Loops with the same head are one loop (two back edges).
An inner loop is its own loop: its head has entry edges from the enclosing
loop's body and its exits return into that body. The CFG with its back edges
removed is acyclic for a reducible function; reachability on it is what a
seed at a loop head depends on, because the head's seed comes from its entry
edges and its back edges are separate edge obligations.

A cyclic strongly connected component without a dominating head (irreducible
code) has no natural loop; its `minimum_pc` row of FUNCTION.json `loops`
(tools/stock_zisk/inventory.py cfg_loops) still names a cut, as before.
"""


def _pc(value):
    return int(value, 0) if isinstance(value, str) else int(value)


def block_successors(function):
    return {_pc(block['start']): sorted({_pc(target) for target in block['successors']})
            for block in function['blocks']}


def dominators(successors, entry):
    """{block: set of its dominators} for the blocks reachable from entry."""
    order, seen, stack = [], set(), [(entry, iter(successors.get(entry, [])))]
    seen.add(entry)
    while stack:
        node, children = stack[-1]
        child = next(children, None)
        if child is None:
            order.append(node)
            stack.pop()
        elif child not in seen and child in successors:
            seen.add(child)
            stack.append((child, iter(successors.get(child, []))))
    order.reverse()   # reverse postorder
    predecessors = {node: [] for node in order}
    for node in order:
        for child in successors.get(node, []):
            if child in predecessors:
                predecessors[child].append(node)
    dominator = {node: set(order) for node in order}
    dominator[entry] = {entry}
    changed = True
    while changed:
        changed = False
        for node in order[1:]:
            new = set.intersection(*(dominator[p] for p in predecessors[node])) | {node}
            if new != dominator[node]:
                dominator[node], changed = new, True
    return dominator


def natural_loops(function):
    """One row per loop head, by head pc: head, back_edges, body, entry_edges, exit_edges,
    parent (the innermost enclosing loop head or None) and depth (1 for an outermost loop)."""
    successors = block_successors(function)
    entry = _pc(function['entry'])
    dominator = dominators(successors, entry)
    predecessors = {}
    for node, children in successors.items():
        for child in children:
            predecessors.setdefault(child, set()).add(node)
    back = sorted((node, child) for node in dominator for child in successors[node]
                  if child in dominator[node])
    loops = {}
    for source, head in back:
        row = loops.setdefault(head, {'head': head, 'back_edges': [], 'body': {head}})
        row['back_edges'].append((source, head))
        pending = [source]
        while pending:
            node = pending.pop()
            if node in row['body']:
                continue
            row['body'].add(node)
            pending.extend(p for p in predecessors.get(node, ()) if p in dominator)
    for row in loops.values():
        body = row['body']
        row['entry_edges'] = sorted((p, row['head']) for p in predecessors.get(row['head'], ())
                                    if p not in body and p in dominator)
        row['exit_edges'] = sorted((node, child) for node in body for child in successors[node] if child not in body)
    for row in loops.values():
        outer = [other for other in loops.values() if other is not row and row['head'] in other['body']
                 and row['body'] < other['body']]
        row['parent'] = min(outer, key=lambda other: len(other['body']))['head'] if outer else None
    for row in loops.values():
        depth, parent = 1, row['parent']
        while parent is not None:
            depth, parent = depth + 1, loops[parent]['parent']
        row['depth'] = depth
        row['body'] = sorted(row['body'])
    return [loops[head] for head in sorted(loops)]


def back_edges(function):
    return {edge for row in natural_loops(function) for edge in row['back_edges']}


def loop_heads(function):
    """Every natural loop head, and the `minimum_pc` of every FUNCTION.json loop row."""
    return ({row['head'] for row in natural_loops(function)}
            | {_pc(loop['minimum_pc']) for loop in function.get('loops', [])})


def forward_successors(function):
    """The block successors without the back edges."""
    removed = back_edges(function)
    return {node: [child for child in children if (node, child) not in removed]
            for node, children in block_successors(function).items()}


LOAD_SIZES = {'lb': 1, 'lbu': 1, 'lh': 2, 'lhu': 2, 'lw': 4, 'lwu': 4, 'ld': 8}
STORE_SIZES = {'sb': 1, 'sh': 2, 'sw': 4, 'sd': 8}
NO_DESTINATION = set(STORE_SIZES) | {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'j', 'jr', 'ret', 'ecall', 'fence'}


def cursor_accesses(function, head, register):
    """The loads and stores of the loop at `head` whose address register is `register` (`xN`)
    while it still holds the value it had at the start of its block: [{pc, kind, offset, size}].
    Blocks of inner loops are left to their own loop."""
    number = int(register[1:])
    loops = {row['head']: row for row in natural_loops(function)}
    loop = loops[_pc(head)]
    inner = {pc for row in loops.values() if row['parent'] == loop['head'] for pc in row['body']}
    rows = sorted(function['rows'], key=lambda row: _pc(row['pc']))
    accesses = []
    for block in function['blocks']:
        start, end = _pc(block['start']), _pc(block['end'])
        if start not in loop['body'] or start in inner:
            continue
        for row in rows:
            if not start <= _pc(row['pc']) < end:
                continue
            mnemonic = row.get('mnemonic')
            size = LOAD_SIZES.get(mnemonic) or STORE_SIZES.get(mnemonic)
            if size and row.get('rs1') == number:
                accesses.append({'pc': _pc(row['pc']), 'kind': 'load' if mnemonic in LOAD_SIZES else 'store',
                                 'offset': int(row.get('imm') or 0), 'size': size})
            if mnemonic not in NO_DESTINATION and row.get('rd') == number:
                break   # The register no longer holds the cursor in the rest of this block.
    return accesses


def cursor_width(function, head, register, stride):
    """The bytes one iteration accesses at the cursor `register`: the largest offset + size of
    its accesses (1 without one). An access before the cursor, or a window wider than the stride
    (the loop guard bounds the cursor, not the last bytes of its window), is refused."""
    accesses = cursor_accesses(function, head, register)
    if any(row['offset'] < 0 for row in accesses):
        raise ValueError('The loop at %s accesses memory before its cursor %s (%s); the cursor rows need a '
                         'hand design' % (hex(_pc(head)), register, ', '.join(hex(row['pc']) for row in accesses
                                                                              if row['offset'] < 0)))
    width = max([row['offset'] + row['size'] for row in accesses] or [1])
    if width > stride:
        raise ValueError('The loop at %s accesses %d bytes at its cursor %s per iteration with stride %d: the '
                         'loop guard bounds the cursor, not the end of its window; a design must state the '
                         'window (`width`) and its bound' % (hex(_pc(head)), width, register, stride))
    return width
