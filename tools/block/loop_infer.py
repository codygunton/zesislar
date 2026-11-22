"""Infer the structural part of a loop design from the code (no hand data).

For every natural loop head (loop_structure) without a hand design, `infer_designs` writes a
design row in the format of the profile's `loop_designs` (loop_design.py reads both alike):

- `head`, `entry_predecessor`: the head and the source of its one entry edge (a head with
  several entry edges is refused: the class is built from one entry edge);
- `registers`: the general registers the loop body writes (inner loops included) that are live
  at the head, each with a fresh binder `loop_<reg>`;
- `index`: `i`, `i2`, ... by nesting depth, so an inner class never shadows its outer index;
- facts, each TRUE BY CONSTRUCTION (implied at the entry edge with index 0 and preserved by
  every back edge, whatever the data):
  * `index_range`: `0 <= i`;
  * `index_link` of a register the body advances by one `addi r, r, K` in a block that runs on
    every iteration (it dominates every back-edge source): the modular sum
    `bv_unsigned loop_r = (bv_unsigned {r} + K * i) mod 2 ^ 64`;
  * `guard` of a latch whose only back edge is taken on an unsigned comparison of an advanced
    register with a register the body leaves unchanged: `i = 0 \\/ <comparison>` (the
    comparison holds on every back edge; index 0 is the entry);
- `array_cursor` for every advanced register that addresses memory in the body: its stride, and
  `array: null` (loop_design.loop_head_seed takes the one owned array whose base is an addend
  of the register's entry value); the width comes from the code (loop_structure.cursor_width).

What only a person or a contract can supply stays out: bounds that need the entry facts or the
contract (cursor within its array, a length relation), and every meaning fact. A hand design for
a head replaces the inferred one.
"""
import re

from loop_structure import (LOAD_SIZES, NO_DESTINATION, STORE_SIZES, block_successors, dominators,
                            natural_loops, _pc)

UNSIGNED = {'bltu': '<', 'bgeu': '>='}


def _rows_by_block(function):
    rows = sorted(function['rows'], key=lambda row: _pc(row['pc']))
    return {_pc(block['start']): [row for row in rows if _pc(block['start']) <= _pc(row['pc']) < _pc(block['end'])]
            for block in function['blocks']}


def _writes(row):
    return row.get('mnemonic') not in NO_DESTINATION and row.get('rd') not in (None, 0)


def infer_design(function, loop, profile_key=hex, live=None):
    """The inferred design row of one natural loop (a row of natural_loops), or raise ValueError."""
    head = loop['head']
    if len(loop['entry_edges']) != 1:
        raise ValueError('The loop head %s has %d entry edges; an inferred design needs exactly one'
                         % (hex(head), len(loop['entry_edges'])))
    by_block = _rows_by_block(function)
    body_rows = [row for pc in loop['body'] for row in by_block[pc]]
    written = sorted({row['rd'] for row in body_rows if _writes(row)})
    registers = ['x%d' % number for number in written if live is None or 'x%d' % number in live]
    index = 'i' if loop['depth'] == 1 else 'i%d' % loop['depth']
    dominator = dominators(block_successors(function), _pc(function['entry']))
    every_iteration = {pc for pc in loop['body'] if all(pc in dominator[source] for source, _ in loop['back_edges'])}
    strides = {}
    for register in registers:
        number = int(register[1:])
        writes = [(pc, row) for pc in loop['body'] for row in by_block[pc] if _writes(row) and row['rd'] == number]
        if (len(writes) == 1 and writes[0][1]['mnemonic'] == 'addi' and writes[0][1].get('rs1') == number
                and writes[0][0] in every_iteration and int(writes[0][1].get('imm') or 0) != 0):
            strides[register] = int(writes[0][1]['imm'])
    facts = [{'kind': 'index_range', 'coq': '(0 <= %s)%%Z' % index}]
    for register, stride in sorted(strides.items(), key=lambda item: int(item[0][1:])):
        facts.append({'kind': 'index_link', 'stride': stride,
                      'coq': 'bv_unsigned loop_%s = ((bv_unsigned {%s} + %d * %s) mod 2 ^ 64)%%Z'
                             % (register, register, stride, index)})
    unchanged = {number for number in range(1, 32) if number not in written}
    for source, _ in loop['back_edges']:
        branch = by_block[source][-1] if by_block[source] else None
        successors = block_successors(function)[source]
        if branch is None or branch.get('mnemonic') not in UNSIGNED or len(successors) != 2:
            continue
        # The taken target: the row's successor that is not the next instruction (the row's
        # immediate field is the raw encoding).
        taken = [_pc(target) for target in branch.get('successors', [])
                 if _pc(target) != _pc(branch['pc']) + int(branch.get('size', 4))]
        if taken != [head]:
            continue   # The back edge is the fall-through: its condition is the negation; left to a design.
        left, right = branch.get('rs1'), branch.get('rs2')
        operands = ['x%d' % left, 'x%d' % right]
        if not set(operands) & set(strides) or not all(r in strides or int(r[1:]) in unchanged for r in operands):
            continue

        def term(number):
            return 'bv_unsigned ' + ('loop_x%d' % number if 'x%d' % number in strides else '{x%d}' % number)
        facts.append({'kind': 'guard', 'coq': '(%s = 0 \\/ %s %s %s)%%Z' % (index, term(left), UNSIGNED[branch['mnemonic']],
                                                                       term(right))})
    cursors = []
    for register, stride in sorted(strides.items(), key=lambda item: int(item[0][1:])):
        number = int(register[1:])
        if stride > 0 and any((LOAD_SIZES.get(row.get('mnemonic')) or STORE_SIZES.get(row.get('mnemonic')))
                              and row.get('rs1') == number for row in body_rows):
            cursors.append({'register': register, 'array': None, 'stride': stride,
                            'extent_reason': 'inferred: the loop body accesses memory at %s, which advances by %d '
                                             'per iteration; its range is an open read obligation of the body'
                                             % (register, stride)})
    design = {'head': profile_key(head), 'entry_predecessor': profile_key(loop['entry_edges'][0][0]),
              'registers': {register: 'loop_' + register for register in registers}, 'index': index,
              'facts': facts, 'inferred': True}
    if cursors:
        design['array_cursor'] = cursors
    return design


def infer_designs(function, hand_designs, profile_pc=lambda key: key, profile_key=hex, liveness=None):
    """(designs, refusals): an inferred design for every natural loop head without a hand design,
    outer loops first; `refusals` maps a head to the reason it has none."""
    hand = {int(profile_pc(row['head']), 0) for row in hand_designs}
    designs, refusals = [], {}
    for loop in sorted(natural_loops(function), key=lambda row: (row['depth'], row['head'])):
        if loop['head'] in hand:
            continue
        try:
            designs.append(infer_design(function, loop, profile_key,
                                        None if liveness is None else liveness.get(hex(loop['head']))))
        except ValueError as error:
            refusals[hex(loop['head'])] = str(error)
    return designs, refusals
