"""Create the approved exact-object replay view inside a source scope."""
import argparse
from pathlib import Path
import sys

sys.path[:0] = [str(Path(__file__).resolve().parent / 'code'), str(Path(__file__).resolve().parents[1])]
from command_scope import require
from replay_object_view import create


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec', type=Path, required=True)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require()
    print(create({'path': str(args.spec.resolve()), 'sha256': args.sha256}, args.output))


if __name__ == '__main__':
    main()
