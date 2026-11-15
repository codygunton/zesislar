#!/usr/bin/env python3
"""Save residual goal files into the persistent store `_build/goals/<function>/<case>/<tag>/`.

usage: tools/save_goal.py --function F --case C --tag T [--head H] [--bank B] [--command CMD] FILE...

Copies each FILE (at most 1 MiB) and writes MANIFEST.json with head, bank, command and date.
cleanup_after_merge.sh and the build janitor never delete the store. --head defaults to the
HEAD of the current checkout.
"""

import argparse
from pathlib import Path
import subprocess
import sys

from build_janitor import base_root
import goal_store


def current_head():
    result = subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True)
    return result.stdout.strip() if result.returncode == 0 else None


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--function', required=True, help='function, e.g. decodeItem')
    parser.add_argument('--case', required=True, help='block or goal class, e.g. 0300')
    parser.add_argument('--tag', required=True, help='name of this save, e.g. lia-residual-1')
    parser.add_argument('--head', help='commit the goals come from (default: HEAD here)')
    parser.add_argument('--bank', help='bank the goals compile against')
    parser.add_argument('--command', help='command that produced the goals')
    parser.add_argument('--root', help='base checkout (default: owner of the Git common dir)')
    parser.add_argument('files', nargs='+')
    args = parser.parse_args(argv)
    names = [Path(file).name for file in args.files]
    if len(set(names)) != len(names):
        parser.error('two files have the same name; save them under different tags')
    try:
        directory = goal_store.save(args.root or base_root(), args.function, args.case, args.tag,
                                    list(zip(args.files, names)), head=args.head or current_head(),
                                    bank=args.bank, command=args.command)
    except (OSError, ValueError) as error:
        print(f'save_goal: {error}', file=sys.stderr)
        return 1
    print(directory)
    return 0


if __name__ == '__main__':
    sys.exit(main())
