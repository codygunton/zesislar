#!/usr/bin/env python3
"""Check or render solver-policy declarations from the single policy table."""
from pathlib import Path
import argparse
import json
import sys


def render(policy):
    if policy.get('version') != 1:
        raise ValueError('Unsupported solver policy version.')
    for key in ('prop_facts', 'kernel_nodes'):
        if type(policy.get(key)) is not int or policy[key] <= 0:
            raise ValueError(f'{key} must be a positive integer.')
    if policy.get('exceptions') != []:
        raise ValueError('Solver exceptions require reviewed implementation support.')
    return (
        '(* Generated declarations from Evidence/solver_context_policy.json. *)\n'
        'From Coq Require Import ZArith.ZArith Lists.List Strings.String.\n'
        f'Definition zesu_solver_prop_limit : Z := {policy["prop_facts"]}.\n'
        f'Definition zesu_solver_node_limit : Z := {policy["kernel_nodes"]}.\n'
        'Definition zesu_solver_exception_labels : list string := nil.\n'
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = root / 'ZesuSsz/Evidence/solver_context_policy.json'
    target = root / 'ZesuSsz/Automation2/SolverContextPolicy.v'
    expected = render(json.loads(source.read_text(encoding='utf-8')))
    if args.write:
        target.write_text(expected, encoding='utf-8')
    elif target.read_text(encoding='utf-8') != expected:
        raise ValueError('Solver policy declarations are stale. Run with --write.')
    print('Solver policy declarations match the single policy table.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as error:
        print(f'solver policy: {error}', file=sys.stderr)
        sys.exit(1)
