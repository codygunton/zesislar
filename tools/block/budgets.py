#!/usr/bin/env python3
"""Step budgets of a charged function's entries (plan Stage T, T5).

    budgets.py --function F [--profile PATH] [--cfg CFG] [--run DIR [--round N]]
               [--callee-budget SYMBOL=BUDGET ...] [--compute-callees]

One unit is one instruction fetch. An entry's budget pays for every instruction fetched from that entry
on, its own first instruction included: for a block start b,

    B(b) = instructions(b) + max over the successor edges of b of the edge's term

where the term of an edge is
  * into a block of the function: B(successor);
  * a call (the block ends in a `call` row): the callee's budget plus B(return site);
  * a tail call (the block jumps to another function's entry): the callee's budget;
  * a function return: 0.
A block of an `unreachable_entries` row has budget 0 and is no successor. At a loop cut with a
`potential` row (profile key `potentials` {block: {"potential": P, "entry_bound"?: E}}) B is P itself,
not computed. An edge into a cut from a block of the cut's loop (one the cut reaches) has the term P
over the loop body's binders; the inequality between the potential before and after the iteration is
left to the block's proof. An edge into a cut from outside its loop (the entry edge) has the term P
with each register binder of the cut (the loop design's `registers`) read as that register's value
at the predecessor's entry; a binder the predecessor writes or a binder without a register cannot be
read there, and the term is the row's `entry_bound` E (an expression in scope at every entry: over
`args`, `returnAddress`); with neither the budget is refused. A cycle that no `potential` row breaks
is refused with the offset of the loop head where the walk re-enters it.

A callee's budget is the `budget` field of its row in ZesuSsz/Contracts/proved_functions.json (the
row whose `symbol` is the call target's symbol): an integer, or a Coq Z expression over the call's
argument registers written `{argv:N}` (the 64-bit value of x(10+N) at the call, the placeholder of
call rows). `--callee-budget SYMBOL=BUDGET` overrides it; `--compute-callees` computes a callee
without one from the CFG the same way (a callee with a loop is then refused).

Texts. A budget is an integer while no expression enters it. `{reg:xR}` in a budget is the 64-bit
value of register xR at the entry the budget belongs to; it moves to a predecessor only through a
block that does not write xR (a call writes every caller-saved register), and an argument
placeholder of a callee's budget becomes `{reg:x(10+N)}` at its call block's entry when the block
does not write x(10+N) before the call. The renderer reads `{reg:xR}` as the register's value in each
alternative of the entry. Maxima fold their literal arms: every expression arm is nonnegative (a
step budget states 0 <= z), so max(k, e + c) <= e + max(k, c); `Z.max` appears only between two
different expression arms.

Output: BUDGETS.json (`--run DIR`: DIR/round-<n>/derived/BUDGETS.json; the latest round without
`--round`), per entry: the budget, the instruction count and the successor terms; on stdout the
function's entry budget.
"""
from pathlib import Path
import argparse
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
CFG = ROOT / 'build/stock-zisk/cfg.json'
REGISTRY = ROOT / 'ZesuSsz/Contracts/proved_functions.json'
SCHEMA = 'zesu.budgets.v1'
# The registers a call may change: ra, t0-t2, a0-a7, t3-t6.
CALLER_SAVED = {1, 5, 6, 7, *range(10, 18), *range(28, 32)}
ALL_REGISTERS = set(range(1, 32))
WRITING_KINDS = ('plain', 'load', 'jump', 'call', 'return', 'indirect')
REGISTER = re.compile(r'\{reg:x(\d+)\}')
ARGUMENT = re.compile(r'\{argv:(\d+)\}')
IDENTIFIER = re.compile(r"(?<![\w'.])[A-Za-z_][\w']*(?![\w'.])")


class BudgetError(ValueError):
    """A budget the walk cannot state."""


class Budget:
    """`expression + constant`: expression None (a literal) or a Coq Z text that is >= 0."""

    __slots__ = ('expression', 'constant')

    def __init__(self, expression=None, constant=0):
        self.expression, self.constant = expression, constant

    @classmethod
    def of(cls, value):
        """A budget from an integer or a Coq Z text (a digit string is a literal)."""
        if isinstance(value, Budget):
            return value
        if isinstance(value, int):
            return cls(None, value)
        text = str(value).strip()
        if re.fullmatch(r'\d+', text):
            return cls(None, int(text))
        return cls(parenthesized(text), 0)

    @property
    def literal(self):
        return self.expression is None

    def __add__(self, other):
        other = Budget.of(other)
        if self.literal or other.literal:
            return Budget(self.expression or other.expression, self.constant + other.constant)
        return Budget(self.expression + ' + ' + other.expression, self.constant + other.constant)

    def __eq__(self, other):
        return isinstance(other, Budget) and (self.expression, self.constant) == (other.expression, other.constant)

    def text(self):
        if self.literal:
            return str(self.constant)
        return self.expression + (' + %d' % self.constant if self.constant else '')

    def json(self):
        return self.constant if self.literal else self.text()

    def __repr__(self):
        return 'Budget(%s)' % self.text()


def maximum(budgets):
    """An upper bound of the maximum: literals fold into the constant (see the module text)."""
    budgets = [Budget.of(budget) for budget in budgets]
    if not budgets:
        return Budget(None, 0)
    literal = max([budget.constant for budget in budgets if budget.literal], default=None)
    arms = {}
    for budget in budgets:
        if not budget.literal:
            arms[budget.expression] = max(arms.get(budget.expression, budget.constant), budget.constant)
    if not arms:
        return Budget(None, literal)
    base = min(arms.values())
    terms = sorted(expression + (' + %d' % (constant - base) if constant > base else '')
                   for expression, constant in arms.items())
    expression = terms[0]
    for term in terms[1:]:
        expression = '(Z.max %s %s)' % (parenthesized(expression), parenthesized(term))
    return Budget(expression, base if literal is None else max(base, literal))


def parenthesized(text):
    """`text` as one Coq argument: itself when one parenthesis pair encloses all of it."""
    if text.startswith('('):
        depth = 0
        for index, char in enumerate(text):
            depth += {'(': 1, ')': -1}.get(char, 0)
            if depth == 0:
                if index == len(text) - 1:
                    return text
                break
    return '(' + text + ')'


def registers_of(budget):
    return {int(number) for number in REGISTER.findall(budget.expression or '')}


def load_cfg_function(symbol, cfg=CFG):
    data = json.loads(Path(cfg).read_text())
    for function in data['functions']:
        if function['name'] == symbol:
            return function, data
    raise BudgetError('the CFG %s has no function %s' % (cfg, symbol))


def registry_budgets(registry=REGISTRY):
    """{symbol: budget} of the registry rows with a `budget` field."""
    rows = json.loads(Path(registry).read_text())['functions']
    return {row['symbol']: row['budget'] for row in rows if 'budget' in row and row.get('symbol')}


def potential_binders(profile, key):
    """{binder name: register number} of the loop design at block `key` (its register binders)."""
    for design in (profile.get('loop_designs') or []) if profile is not None else []:
        if profile.key(profile.pc(design['head'])) == key:
            return {name: int(register[1:]) for register, name in design.get('registers', {}).items()}
    return {}


class Walk:
    """The budgets of one function's blocks (see the module text)."""

    def __init__(self, function, profile=None, callee_budget=None, functions=(), compute_callees=False,
                 registry=None):
        self.function, self.profile = function, profile
        self.entry = function['entry']
        self.rows = {row['pc']: row for row in function['rows']}
        self.blocks = {block['start']: block for block in function['blocks']}
        self.calls = {call['pc']: call for call in function['calls']}
        self.functions = {item['entry']: item for item in functions}
        self.callee_budget = dict(callee_budget or {})
        self.registry = registry if registry is not None else {}
        self.compute_callees = compute_callees
        self.callees = {}
        get = (lambda key, default: profile.get(key, default)) if profile is not None else (lambda key, default: default)
        self.unreachable = {self._address(key) for key in get('unreachable_entries', [])}
        self.potentials = {self._address(key): row for key, row in (get('potentials', {}) or {}).items()}
        for address in self.potentials:
            if address not in self.blocks:
                raise BudgetError('a potential row at %s names no block start' % self.offset(address))
        self.memo, self.visiting, self.records = {}, [], {}

    def _address(self, key):
        return int(self.profile.pc(key), 16) if self.profile is not None else self.entry + int(key, 16)

    def offset(self, address):
        return '+0x%x' % (address - self.entry)

    def key(self, address):
        return format(address - self.entry, '04x')

    def instructions(self, block):
        return [self.rows[pc] for pc in sorted(self.rows) if block['start'] <= pc < block['end']]

    def writes(self, rows):
        written = set()
        for row in rows:
            if row['kind'] == 'runtime':
                return set(ALL_REGISTERS)
            if row['kind'] in WRITING_KINDS and row.get('rd'):
                written.add(row['rd'])
            if row['kind'] == 'call':
                written |= CALLER_SAVED
        return written

    def through(self, budget, rows, start, what):
        """`budget` at the entry of `rows`: refused when a placeholder register is written there."""
        written = registers_of(budget) & self.writes(rows)
        if written:
            raise BudgetError('the budget %s of %s reads %s, which the block at %s writes'
                              % (budget.text(), what, ', '.join('x%d' % number for number in sorted(written)),
                                 self.offset(start)))
        return budget

    # ------------------------------------------------------------------ callees
    def callee(self, target):
        """The budget of the function at `target` (registry, override, or computed)."""
        function = self.functions.get(target)
        symbol = function['name'] if function else hex(target)
        if symbol in self.callees:
            return Budget.of(self.callees[symbol]['budget'])
        if symbol in self.callee_budget:
            value, source = self.callee_budget[symbol], 'override'
        elif symbol in self.registry:
            value, source = self.registry[symbol], 'registry'
        elif self.compute_callees and function is not None:
            try:
                walk = Walk(function, functions=self.functions.values(), callee_budget=self.callee_budget,
                            compute_callees=True, registry=self.registry)
                budget = walk.entry_budget()
            except BudgetError as error:
                raise BudgetError('callee %s: %s' % (symbol, error))
            value, source = callee_text(budget), 'computed'
            self.callees.update(walk.callees)
        else:
            raise BudgetError('the callee %s has no budget (registry field `budget`)' % symbol)
        self.callees[symbol] = {'budget': Budget.of(value).json(), 'source': source}
        return Budget.of(value)

    # ------------------------------------------------------------------ walk
    def budget(self, address):
        if address in self.unreachable:
            return Budget(None, 0)
        if address in self.potentials:
            return Budget.of(self.potentials[address]['potential'])
        if address in self.memo:
            return self.memo[address]
        if address in self.visiting:
            raise BudgetError('the loop at %s has no potential row' % self.offset(address))
        if address not in self.blocks:
            raise BudgetError('%s is no block start of %s' % (self.offset(address), self.function['name']))
        self.visiting.append(address)
        try:
            result = self._block(address)
        finally:
            self.visiting.pop()
        self.memo[address] = result
        return result

    def _block(self, address):
        block = self.blocks[address]
        rows = self.instructions(block)
        last = rows[-1]
        terms = []
        call = self.calls.get(last['pc'])
        for call_pc in self.calls:
            if block['start'] <= call_pc < block['end'] and call_pc != last['pc']:
                raise BudgetError('the call at %s is not the last instruction of its block' % self.offset(call_pc))
        inside = [target for target in block['successors'] if self.entry <= target < self.function['end']]
        outside = [target for target in block['successors'] if target not in inside]
        if call is not None and call['kind'] == 'tail' or outside:
            if call is None or call['kind'] != 'tail' or outside != [call['target']] or inside:
                raise BudgetError('the block at %s leaves the function without a call row' % self.offset(address))
            terms.append({'kind': 'tail_call', 'to': symbol_of(self, call['target']),
                          'term': self._argument_budget(call, rows, address)})
        elif call is not None:
            callee = self._argument_budget(call, rows, address)
            for target in inside:
                after = self.through(self.successor_term(address, target), rows, address,
                                     'the return site ' + self.offset(target))
                terms.append({'kind': 'call', 'to': self.offset(target), 'callee': symbol_of(self, call['target']),
                              'term': callee + after})
        elif last['kind'] == 'return' or not block['successors']:
            terms.append({'kind': 'function_return', 'term': Budget(None, 0)})
        else:
            for target in inside:
                if target in self.unreachable:
                    continue
                term = self.successor_term(address, target)
                if target not in self.potentials or not self.in_loop(target, address):
                    term = self.through(term, rows, address, self.offset(target))
                terms.append({'kind': self.edge_kind(address, target), 'to': self.offset(target), 'term': term})
        result = Budget(None, len(rows)) + maximum([term['term'] for term in terms])
        self.records[address] = {'pc': hex(address), 'offset': self.offset(address), 'instructions': len(rows),
                                 'budget': result, 'successors': terms}
        return result

    def _argument_budget(self, call, rows, address):
        """The callee's budget at the call block's entry: `{argv:N}` read as x(10+N) there."""
        budget = self.callee(call['target'])
        if budget.literal:
            return budget
        before = [row for row in rows if row['pc'] < call['pc']]
        written = self.writes(before)

        def register(match):
            number = 10 + int(match[1])
            if number in written:
                raise BudgetError('the budget of the callee at %s reads argument %s, which the block at %s '
                                  'writes before the call' % (self.offset(call['pc']), match[1],
                                                               self.offset(address)))
            return '{reg:x%d}' % number
        return Budget(ARGUMENT.sub(register, budget.expression), budget.constant)

    def in_loop(self, cut, address):
        """Whether `cut` reaches `address` (the edge address -> cut closes the cut's loop)."""
        seen, todo = set(), [cut]
        while todo:
            node = todo.pop()
            if node == address:
                return True
            if node in seen or node not in self.blocks:
                continue
            seen.add(node)
            todo.extend(target for target in self.blocks[node]['successors']
                        if self.entry <= target < self.function['end'] and target not in self.unreachable)
        return False

    def edge_kind(self, address, target):
        if target in self.potentials:
            return 'back_edge' if self.in_loop(target, address) else 'loop_entry'
        return 'edge'

    def successor_term(self, address, target):
        if target not in self.potentials:
            return self.budget(target)
        row = self.potentials[target]
        potential = Budget.of(row['potential'])
        if self.in_loop(target, address):
            return potential
        # The entry edge: the cut's register binders are the registers after the predecessor.
        binders = potential_binders(self.profile, self.key(target))
        text = row['potential']
        names = set(IDENTIFIER.findall(text))
        loose = [name for name in names if name in self.loop_binders(target) and name not in binders]
        written = self.writes(self.instructions(self.blocks[address]))
        moved = [name for name in names if name in binders and binders[name] in written]
        if not loose and not moved:
            for name, number in binders.items():
                text = re.sub(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'.])", '{reg:x%d}' % number, text)
            return Budget.of(text)
        if row.get('entry_bound'):
            return Budget.of(row['entry_bound'])
        raise BudgetError('the potential of the loop at %s cannot be stated at its entry from %s (%s); '
                          'give its potential row an entry_bound'
                          % (self.offset(target), self.offset(address),
                             ', '.join(sorted(loose + moved))))

    def loop_binders(self, target):
        """Every binder name of the loop-cut design at `target` (registers, index, owned binders)."""
        names = set(potential_binders(self.profile, self.key(target)))
        for design in (self.profile.get('loop_designs') or []) if self.profile is not None else []:
            if self.profile.key(self.profile.pc(design['head'])) == self.key(target):
                if design.get('index'):
                    names.add(design['index'])
                names |= {binder['name'] for binder in (design.get('owned') or {}).get('binders', [])}
        names |= set(self.potentials.get(target, {}).get('binders', []))
        return names

    def entry_budget(self):
        return self.budget(self.entry)

    def run(self):
        """Every block's record: from the entry, from each cut's successors, then the rest."""
        self.entry_budget()
        for cut in sorted(self.potentials):
            self.visiting = [cut]
            self._block(cut)
            self.visiting = []
        for address in sorted(self.blocks):
            if address not in self.unreachable and address not in self.records:
                self.budget(address)
        entries = {}
        for address in sorted(self.blocks):
            key = self.key(address)
            if address in self.unreachable:
                entries[key] = {'pc': hex(address), 'offset': self.offset(address), 'kind': 'unreachable',
                                'budget': 0, 'instructions': len(self.instructions(self.blocks[address])),
                                'successors': []}
                continue
            record = dict(self.records[address])
            record['successors'] = [{**term, 'term': term['term'].json()} for term in record['successors']]
            if address in self.potentials:
                record.update(kind='loop_cut', budget=Budget.of(self.potentials[address]['potential']).json(),
                              computed=record['budget'].json())
            else:
                record.update(kind='block', budget=record['budget'].json())
            entries[key] = record
        return {'schema': SCHEMA, 'function': self.function['name'], 'entry': hex(self.entry),
                'entry_budget': self.budget(self.entry).json(), 'entries': entries,
                'callees': dict(sorted(self.callees.items())),
                'convention': 'an entry budget pays for every instruction fetched from that entry on, its first '
                              'instruction included; one unit is one instruction fetch'}


def symbol_of(walk, target):
    function = walk.functions.get(target)
    return function['name'] if function else hex(target)


def callee_text(budget):
    """A callee's entry budget as a call-row budget: `{reg:xR}` of an argument register is `{argv:N}`."""
    if budget.literal:
        return budget.constant

    def argument(match):
        number = int(match[1])
        if not 10 <= number <= 17:
            raise BudgetError('a callee budget reads x%d, which is no argument register' % number)
        return '{argv:%d}' % (number - 10)
    return REGISTER.sub(argument, budget.text())


def callee_budget(address, cfg=None, registry=None):
    """The registry budget of the function whose entry is `address` (a call row's callee)."""
    names = {function['entry']: function['name']
             for function in json.loads(Path(cfg or CFG).read_text())['functions']}
    symbol = names.get(address)
    budgets = registry_budgets(registry or REGISTRY)
    if symbol not in budgets:
        raise BudgetError('the callee %s has no budget (registry field `budget`)' % (symbol or hex(address)))
    return Budget.of(budgets[symbol])


def entry_budgets(profile, cfg=None, registry=None, overrides=None, compute_callees=False):
    """The BUDGETS.json record of a profile's function (the renderers' entry point)."""
    symbol = profile.get('cfg_function') or profile.get('symbol')
    function, data = load_cfg_function(symbol, cfg or CFG)
    walk = Walk(function, profile, callee_budget=overrides, functions=data['functions'],
                compute_callees=compute_callees, registry=registry_budgets(registry or REGISTRY))
    return walk.run()


def budget_text(record, key):
    """The Coq text of the budget of entry `key` in a BUDGETS.json record."""
    return Budget.of(record['entries'][key]['budget']).text()


def read_register(text, register):
    """The value of `"xR" ↦ᵣ (RVal_Bits (VALUE : bv 64%N))` (outer parenthesis optional) in a rendered
    component, or None."""
    found = re.search(r'"x%d" ↦ᵣ \(?RVal_Bits \(' % register, text)
    if found is None:
        return None
    position, depth = found.end(), 1
    for index in range(position, len(text)):
        if text[index] == '(':
            depth += 1
        elif text[index] == ')':
            depth -= 1
            if depth == 0:
                value = text[position:index]
                return re.sub(r'\s*:\s*bv 64%N\s*$', '', value)
    return None


def resolve_registers(text, components):
    """`text` with each `{reg:xR}` read from the rendered register components of one alternative."""
    def value(match):
        for component in components:
            found = read_register(component, int(match[1]))
            if found is not None:
                return '(' + found + ')'
        raise BudgetError('the budget reads x%s, which the entry does not own' % match[1])
    return REGISTER.sub(value, text)


def budget_conjunct(text):
    """`step_budget (<text>)`, one parenthesis pair around the budget."""
    return 'step_budget ' + parenthesized(str(text))


def place_budget(kinds):
    """Index at which the budget goes among an alternative's components (`kinds`, in order): before
    its first pure fact, else before its continuation, else last."""
    for index, kind in enumerate(kinds):
        if kind == 'pure':
            return index
    for index, kind in enumerate(kinds):
        if kind in ('continuation', 'true'):
            return index
    return len(kinds)


def output_path(run, round_number=None):
    run = Path(run)
    if round_number is None:
        rounds = sorted(int(path.name.split('-', 1)[1]) for path in run.glob('round-*')
                        if path.name.split('-', 1)[1].isdigit())
        round_number = rounds[-1] if rounds else 1
    return run / ('round-%d' % round_number) / 'derived' / 'BUDGETS.json'


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--function', required=True, help='profile name, or a CFG symbol without a profile')
    parser.add_argument('--profile', type=Path, help='profile path (default tools/block/functions/F.json)')
    parser.add_argument('--cfg', type=Path, default=CFG)
    parser.add_argument('--registry', type=Path, default=REGISTRY)
    parser.add_argument('--run', type=Path)
    parser.add_argument('--round', type=int)
    parser.add_argument('--callee-budget', action='append', default=[], metavar='SYMBOL=BUDGET')
    parser.add_argument('--compute-callees', action='store_true')
    options = parser.parse_args(argv)
    overrides = {}
    for item in options.callee_budget:
        symbol, _, value = item.rpartition('=')
        overrides[symbol] = int(value) if value.strip().isdigit() else value
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from function_profiles import PROFILE_DIRECTORY, load_profile
    path = options.profile or PROFILE_DIRECTORY / (options.function + '.json')
    try:
        if path.exists():
            record = entry_budgets(load_profile(str(path)), options.cfg, options.registry, overrides,
                                   options.compute_callees)
        else:
            function, data = load_cfg_function(options.function, options.cfg)
            walk = Walk(function, callee_budget=overrides, functions=data['functions'],
                        compute_callees=options.compute_callees, registry=registry_budgets(options.registry))
            record = walk.run()
    except BudgetError as error:
        print('budgets: refused: %s' % error, file=sys.stderr)
        return 1
    text = json.dumps(record, indent=1) + '\n'
    if options.run:
        output = output_path(options.run, options.round)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text)
        print('wrote', output, file=sys.stderr)
    print(json.dumps({'function': record['function'], 'entry_budget': record['entry_budget'],
                      'callees': record['callees']}))
    return 0


if __name__ == '__main__':
    sys.exit(main())
