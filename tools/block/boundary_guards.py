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
"""
from pathlib import Path
import re
import subprocess

# A cut stop records its boundary before it stops; an infeasible stop has a
# literal False path condition. Neither drops a feasible path.
PASSING_STOPS = frozenset({'handwritten_cut', 'infeasible'})
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


def contradiction_source(header, binders, facts, args_type='DecodeItemArgs'):
    """Return a check that compiles exactly when the facts do not prove False."""
    # The tactic is defined before `Fail`, so an unknown name is an error, not a pass.
    hypotheses = ' ->\n  '.join('(' + fact + ')' for fact in facts)
    return (header + 'Require Import ZesuSsz.Automation2.All.\n\n'
            + 'Ltac zesu_contradiction_check :=\n  ' + CHECK_TACTIC + '.\n\n'
            + 'Goal forall (args : ' + args_type + ') (returnAddress : Z) ' + binders + ',\n  '
            + hypotheses + ' ->\n  False.\nProof.\n  intros.\n'
            + '  Fail solve [zesu_contradiction_check].\nAbort.\n')


class RocqContradictionCheck:
    """Run the contradiction check with one coqc command line."""

    def __init__(self, command, header, directory, args_type='DecodeItemArgs'):
        self.command = [argument for argument in command if argument != '-time']
        self.header = header
        self.args_type = args_type
        self.directory = Path(directory)
        self.runs = []

    def __call__(self, name, binders, facts):
        self.directory.mkdir(parents=True, exist_ok=True)
        path = self.directory / ('Contradiction_' + re.sub(r'\W', '_', name) + '.v')
        path.write_text(contradiction_source(self.header, binders, facts, self.args_type))
        result = subprocess.run(self.command + [path.name], cwd=self.directory,
                                capture_output=True, text=True)
        output = result.stdout + result.stderr
        if result.returncode == 0:
            contradictory = False
        elif NOT_FAILED in output:
            contradictory = True
        else:
            raise BoundaryRefused('The contradiction check did not run for ' + name + ':\n'
                                  + output[-2000:])
        self.runs.append({'name': name, 'check': str(path), 'contradictory': contradictory})
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
