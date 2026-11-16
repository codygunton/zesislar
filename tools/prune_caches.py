#!/usr/bin/env python3
"""Prune the optional per-user harness caches under ~/.cache/zesislar now.

Builds prune them automatically at most once an hour. This runs the same prune
on demand and drains the retired flat binding-digest store completely. Both
caches are disposable: a removed record only costs a rehash or a coqdep query.

    tools/prune_caches.py [--legacy-limit N]

Prints one JSON object with the counts per cache.
"""
import argparse
import json
from pathlib import Path
import sys

sys.path[:0] = [str(Path(__file__).resolve().parent / 'block/harness/code')]
import binding_cache  # noqa: E402
import supplier_resolution_cache  # noqa: E402


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--legacy-limit', type=int, default=None,
                        help='delete at most this many retired v1 files (default: all)')
    args = parser.parse_args(argv)
    report = {'binding_digests': binding_cache.prune(legacy_limit=args.legacy_limit),
              'supplier_import_resolution': supplier_resolution_cache.prune()}
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
