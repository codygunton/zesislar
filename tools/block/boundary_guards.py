"""Refuse generated boundaries whose inventory is incomplete or contradictory.

Guard 1. The forward pass drops a path when it stops it. A boundary that a
dropped path can reach in the CFG has an incomplete alternative inventory, so
a renderer must refuse it. A fault arm that jumps out of the function (to the
trap vector) drops no path to a boundary. A call also jumps out of the function,
but its path resumes at the return site, so a stop at a call drops that path.
The forward pass records these stops on each
boundary as `reaching_stops`; a boundary without that record is refused too.

Guard 2. Each surviving alternative must be consistent. A rendered
alternative definition is refused when its pure facts (path conditions, loop
facts, and the domain fact, which the check unfolds) prove False with the
cursor solver. A generated cut checks each source alternative before it is
generalized, so an infeasible arm cannot widen a register value. The check is a generator-time Rocq run; no proof script is
written into a generated file.

The check reads facts in groups that share no local name: facts over disjoint
names are refuted together only if one group is refuted alone. A group that is
part of a group an earlier check of the same run did not refute is not checked
again, so each fact is checked where it first appears, with the facts it shares
names with.
"""
from pathlib import Path
import os
import re
import subprocess

# A cut stop records its boundary before it stops; an infeasible stop has a
# literal False path condition. Neither drops a feasible path.
PASSING_STOPS = frozenset({'handwritten_cut', 'infeasible', 'call_boundary'})
# A stop of these kinds whose concrete target is outside the function left it.
LEAVING_STOPS = frozenset({'intermediate_pc_mismatch', 'outside_pc'})
ALTERNATIVE = re.compile(r'_(?:ForwardA\d+N\d+|LoopExit)$')
STOP_FIELDS = ('reason', 'block_pc', 'instruction_pc', 'seed_pc', 'path')


class BoundaryRefused(ValueError):
    """A renderer must not emit this boundary."""


def _pc(value):
    return int(value, 0) if isinstance(value, str) else int(value)


def cfg_successors(function):
    return {_pc(block['start']): [_pc(target) for target in block['successors']]
            for block in function['blocks']}


def can_reach(successors, start, target):
    pending, seen = [start], set()
    while pending:
        pc = pending.pop()
        if pc == target:
            return True
        if pc not in seen:
            seen.add(pc)
            pending.extend(successors.get(pc, []))
    return False


def calls_callee(stop, function):
    """The stop's block contains a call whose callee is the stop's concrete target."""
    actual = stop.get('actual_pc')
    if not isinstance(actual, str):
        return False
    start = _pc(stop['block_pc'])
    end = next(_pc(block['end']) for block in function['blocks'] if _pc(block['start']) == start)
    return any(start <= _pc(call['pc']) < end and _pc(call['target']) == _pc(actual)
               for call in function.get('calls', []))


def leaves_function(stop, function):
    """A fault arm jumps to a concrete address outside the function (the trap
    vector). It leaves the function, so it drops no path to a boundary. A jump
    to the callee of a call in the stop's block is a call boundary, not a fault
    exit: the path resumes at the return site."""
    actual = stop.get('actual_pc')
    if (stop['reason'] not in LEAVING_STOPS or not isinstance(actual, str)
            or calls_callee(stop, function)):
        return False
    return not _pc(function['entry']) <= _pc(actual) < _pc(function['end'])


def reaching_stops(stops, successors, target, seeded=None, function=None):
    """Return the stops that dropped a path whose block can reach target.

    A cut stop records its own boundary, but it drops the path beyond the cut.
    When `seeded` names the cuts that have a seed, a stop at an unseeded cut
    reaches every boundary after that cut.
    """
    def dropped(stop):
        if stop['reason'] not in PASSING_STOPS:
            if function is not None and leaves_function(stop, function):
                return False
            return can_reach(successors, _pc(stop['block_pc']), target)
        if stop['reason'] == 'call_boundary':
            # The path resumes at the return site only from a call-return seed.
            site = _pc(stop['target_pc'])
            return (seeded is None or site not in seeded) and can_reach(successors, site, target)
        if stop['reason'] != 'handwritten_cut' or seeded is None or stop.get('target_pc') is None:
            return False
        cut = _pc(stop['target_pc'])
        return cut not in seeded and any(can_reach(successors, after, target)
                                         for after in successors.get(cut, []))
    return [stop for stop in stops if dropped(stop)]


def annotate_reaching_stops(report, function):
    successors = cfg_successors(function)
    seeded = {_pc(boundary['pc']) for boundary in report['boundaries']
              if any(alternative.get('predecessor_pc') is None for alternative in boundary['alternatives'])}
    for boundary in report['boundaries']:
        boundary['reaching_stops'] = [{key: stop.get(key) for key in STOP_FIELDS}
                                      for stop in reaching_stops(report['stops'], successors,
                                                                 _pc(boundary['pc']), seeded, function)]
    return report


def require_complete_boundary(boundary):
    """Raise unless the forward pass shows that no dropped path reaches boundary."""
    pc = boundary.get('pc')
    if 'reaching_stops' not in boundary:
        raise BoundaryRefused('The boundary ' + str(pc) + ' has no stop-reachability record. '
                              'Rerun the forward pass before rendering it.')
    stops = boundary['reaching_stops']
    if stops:
        first = stops[0]
        raise BoundaryRefused(
            str(len(stops)) + ' retained stops can reach the boundary ' + str(pc)
            + '; the first is ' + str(first.get('reason')) + ' in block ' + str(first.get('block_pc'))
            + ' at ' + str(first.get('instruction_pc')) + '.')


def alternative_facts(definition):
    """Return the binder telescope and the pure facts of one rendered definition."""
    start = definition.index(':= ') + 3
    body = definition[start:]
    telescopes = []

    def telescope_end(text, begin):
        position, depth = begin, 0
        while True:
            character = text[position]
            if character == '(':
                depth += 1
            elif character == ')':
                depth -= 1
            elif character == ',' and depth == 0:
                return position
            position += 1

    if body.startswith('(∃ '):
        position = telescope_end(body, 3)
        telescopes.append(body[3:position].strip())
        body = body[position:]
    # A telescope scoped over the facts alone follows the owned resources.
    # An existential inside a pure fact binds only that fact; it is not hoisted.
    pure = [(match.start(), match.end()) for match in re.finditer(r'⌜.*?⌝', body, flags=re.S)]
    for match in re.finditer(r'\(∃ ', body):
        if any(begin <= match.start() < end for begin, end in pure):
            continue
        position = telescope_end(body, match.end())
        telescopes.append(body[match.end():position].strip())
    binders = ' '.join(telescopes)
    facts = re.findall(r'⌜(.*?)⌝', body, flags=re.S)
    if not facts:
        raise BoundaryRefused('The alternative has no pure facts to check.')
    return binders, facts


CHECK_TACTIC = '''ZesuSsz.Automation2.RegisterArrayCursor.zesu_cursor_expose_facts;
  repeat match goal with
    | H : context [bv_signed (bv_add (@bv_zero_extend 64 128 ?v) ?off)] |- _ =>
        rewrite (ZesuSsz.Automation2.BitvectorFacts.zesu_signed_zero_extend_add_64_128 v off
          ltac:(vm_compute; reflexivity)) in H
    end;
    ZesuSsz.Automation2.RegisterArrayCursor.zesu_cursor_linear'''
NOT_FAILED = 'The command has not failed'


LOCAL_NAME = re.compile(r"(?<![\w'.])[A-Za-z_][\w']*")
OUTER_NAMES = ('args', 'returnAddress')


def _closing(text, start):
    """The index of the parenthesis that closes the one at `start`."""
    depth = 0
    for position in range(start, len(text)):
        if text[position] == '(':
            depth += 1
        elif text[position] == ')':
            depth -= 1
            if depth == 0:
                return position
    raise BoundaryRefused('Unbalanced parentheses in a checked fact: ' + text[:200])


def _unwrap(text):
    text = text.strip()
    while text.startswith('(') and _closing(text, 0) == len(text) - 1:
        text = text[1:-1].strip()
    return text


def fact_conjuncts(fact):
    """Split `(A) /\\ (B) /\\ ...` into its conjuncts; the check destructs them anyway."""
    text = _unwrap(fact)
    parts, position = [], 0
    while text.startswith('(', position):
        end = _closing(text, position)
        parts.append(text[position:end + 1])
        position = end + 1
        if text.startswith(' /\\ ', position):
            position += 4
        elif position == len(text):
            break
        else:
            return [fact]
    if len(parts) < 2 or position != len(text):
        return [fact]
    return [conjunct for part in parts for conjunct in fact_conjuncts(part)]


def binder_groups(binders):
    """The parenthesized groups of a binder telescope, with the names each declares."""
    groups, position = [], binders.find('(')
    while position >= 0:
        end = _closing(binders, position)
        text = binders[position:end + 1]
        groups.append((tuple(text[1:].split(':', 1)[0].split()), text))
        position = binders.find('(', end + 1)
    return groups


def check_groups(binders, facts):
    """Split the facts that the check reads into groups that share no local name.

    The check destructs conjunctions, and zesu_cursor_linear clears every hypothesis
    that is not arithmetic, so an existential fact is never read: it is not carried.
    Each group is (binder declarations it names, its facts), in fact order.
    """
    declared = binder_groups(binders)
    local = set(OUTER_NAMES) | {name for names, _ in declared for name in names}
    read = [conjunct for fact in facts for conjunct in fact_conjuncts(fact)
            if not _unwrap(conjunct).startswith(('∃', 'exists '))]
    names = [set(LOCAL_NAME.findall(fact)) & local for fact in read]
    owner, parent = {}, list(range(len(read)))

    def find(index):
        while parent[index] != index:
            parent[index] = parent[parent[index]]
            index = parent[index]
        return index
    for index, mentioned in enumerate(names):
        for name in mentioned:
            if name in owner:
                parent[find(index)] = find(owner[name])
            else:
                owner[name] = index
    members = {}
    for index in range(len(read)):
        members.setdefault(find(index), []).append(index)
    groups = []
    for indices in members.values():
        used = set().union(*(names[index] for index in indices))
        while True:
            texts = [text for group_names, text in declared if used & set(group_names)]
            more = set(LOCAL_NAME.findall(' '.join(texts))) & local
            if more <= used:
                break
            used |= more
        groups.append((texts, [read[index] for index in indices]))
    return groups


def contradiction_source(header, groups, args_type='DecodeItemArgs'):
    """Return a check that compiles exactly when no group of facts proves False."""
    # The tactic is defined before `Fail`, so an unknown name is an error, not a pass.
    goals = ''.join(
        '\nGoal forall (args : ' + args_type + ') (returnAddress : Z)'
        + ''.join(' ' + text for text in declarations) + ',\n  '
        + ' ->\n  '.join('(' + fact + ')' for fact in facts) + ' ->\n  False.\nProof.\n  intros.\n'
        + '  Fail solve [zesu_contradiction_check].\nAbort.\n'
        for declarations, facts in groups)
    return (header + 'Require Import ZesuSsz.Automation2.All.\n\n'
            + 'Ltac zesu_contradiction_check :=\n  ' + CHECK_TACTIC + '.\n' + goals)


class RocqContradictionCheck:
    """Run the contradiction check with one coqc command line."""

    def __init__(self, command, header, directory, args_type='DecodeItemArgs'):
        self.command = [argument for argument in command if argument != '-time']
        self.header = header
        self.args_type = args_type
        self.directory = Path(directory)
        self.runs = []
        # Fact groups that a check of this run did not refute, with that check's file.
        self.checked = []

    def __call__(self, name, binders, facts):
        groups = check_groups(binders, facts)
        keys = [frozenset([('binder', text) for text in declarations] + [('fact', fact) for fact in group_facts])
                for declarations, group_facts in groups]
        pending, reused = [], set()
        for group, key in zip(groups, keys):
            covering = next((path for known, path in self.checked if key <= known), None)
            if covering is None:
                pending.append((group, key))
            else:
                reused.add(covering)
        row = {'name': name, 'groups': len(groups), 'checked_groups': len(pending), 'reused': sorted(reused)}
        if not pending:
            self.runs.append({**row, 'check': None, 'contradictory': False})
            return False
        self.directory.mkdir(parents=True, exist_ok=True)
        path = self.directory / ('Contradiction_' + re.sub(r'\W', '_', name) + '.v')
        path.write_text(contradiction_source(self.header, [group for group, _ in pending], self.args_type))
        result = subprocess.run(self.command + [path.name], cwd=self.directory,
                                capture_output=True, text=True)
        output = result.stdout + result.stderr
        if result.returncode == 0:
            contradictory = False
            self.checked.extend((key, str(path)) for _, key in pending)
        elif NOT_FAILED in output:
            contradictory = True
        else:
            raise BoundaryRefused('The contradiction check did not run for ' + name + ':\n'
                                  + output[-2000:])
        self.runs.append({**row, 'check': str(path), 'contradictory': contradictory})
        return contradictory


def contradictory_alternatives(definitions, check):
    """Return the names of rendered alternatives whose facts prove False."""
    refused = []
    for name, definition in definitions:
        if ALTERNATIVE.search(name):
            binders, facts = alternative_facts(definition)
            if check(name, binders, facts):
                refused.append(name)
    return refused


def contradictory_sources(boundary, render_alone, check):
    """Return the indices of source alternatives whose own facts prove False.

    A cut generalization joins every alternative. One infeasible arm with a
    different register value turns the value that the feasible arms agree on
    into a binder with only a range, and the link to its source is lost. So
    each alternative of a generated cut is rendered alone and checked before
    the cut is generalized. render_alone returns the definitions or None.
    """
    refused = []
    for index, alternative in enumerate(boundary['alternatives']):
        definitions = render_alone({**boundary, 'alternatives': [alternative]})
        if definitions is None:
            continue
        renamed = [(re.sub(r'_ForwardA0(N\d+)$', r'_ForwardA%d\1' % index, name), text)
                   for name, text in definitions]
        if contradictory_alternatives(renamed, check):
            refused.append(index)
    return refused


def refused_alternative_indices(names):
    return sorted({int(re.search(r'_ForwardA(\d+)N\d+$', name).group(1)) for name in names})


def without_alternatives(boundary, indices):
    """Return the boundary without the refused formatter alternatives."""
    if boundary.get('status') != 'generated':
        raise BoundaryRefused('Only a plain generated boundary can drop an alternative: ' + str(boundary.get('pc')))
    kept = [alternative for index, alternative in enumerate(boundary['alternatives']) if index not in indices]
    if not kept:
        raise BoundaryRefused('Every alternative of the boundary ' + str(boundary.get('pc')) + ' proves False.')
    return {**boundary, 'alternatives': kept}


def require_consistent_alternatives(definitions, check):
    refused = contradictory_alternatives(definitions, check)
    if refused:
        raise BoundaryRefused('These alternatives prove False and are refused: ' + ', '.join(refused))
