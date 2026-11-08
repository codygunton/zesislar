#!/usr/bin/env python3
"""Copy a file as a reflink, or refer to it by path and SHA-256.

A reflink copy shares the source's disk extents until one side changes.
It costs no data blocks. This module never falls back to a full copy:
when the filesystem refuses the clone, it raises ReflinkError and leaves
no destination file. Use `reference` when the consumer only reads the file.

    python3 tools/reflink_copy.py SOURCE DESTINATION
    python3 tools/reflink_copy.py --reference PATH
"""

import argparse
import errno
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

# linux/fs.h: _IOW(0x94, 9, int)
FICLONE = 0x40049409


class ReflinkError(OSError):
    """The filesystem refused a reflink copy. No data was copied."""


def reflink_copy(source, destination):
    """Clone SOURCE to DESTINATION and keep its mode and timestamps.

    DESTINATION may be a directory. An existing destination file is
    replaced atomically only after the clone succeeds.
    """
    source = Path(source)
    destination = Path(destination)
    if destination.is_dir():
        destination = destination / source.name
    if not source.is_file():
        raise ReflinkError(errno.EINVAL, 'A reflink source must be a regular file.', str(source))
    if destination.is_symlink():
        raise ReflinkError(errno.EINVAL, 'A reflink destination must not be a symbolic link.',
                           str(destination))
    descriptor, temporary = tempfile.mkstemp(prefix='.' + destination.name + '.reflink-',
                                             dir=destination.parent)
    try:
        with os.fdopen(descriptor, 'wb') as target, source.open('rb') as original:
            try:
                fcntl.ioctl(target.fileno(), FICLONE, original.fileno())
            except OSError as error:
                raise ReflinkError(
                    error.errno,
                    f'The filesystem refused a reflink copy ({os.strerror(error.errno)}). '
                    'No full copy was made. Put the source and destination on one '
                    'reflink-capable filesystem, such as /home (XFS), or refer to the '
                    'source by path and SHA-256.',
                    f'{source} -> {destination}') from error
        shutil.copystat(source, temporary)
        os.replace(temporary, destination)
    finally:
        Path(temporary).unlink(missing_ok=True)
    return destination


def sha256(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def reference(path):
    """Return the path and SHA-256 that a reader checks before it reads."""
    path = Path(path).resolve()
    return {'path': str(path), 'sha256': sha256(path)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--reference', action='store_true',
                        help='print the path and SHA-256 of one file as JSON')
    parser.add_argument('paths', nargs='+')
    args = parser.parse_args(argv)
    if args.reference:
        if len(args.paths) != 1:
            parser.error('--reference takes one path')
        print(json.dumps(reference(args.paths[0])))
        return 0
    if len(args.paths) != 2:
        parser.error('a copy takes a source and a destination')
    try:
        print(reflink_copy(*args.paths))
    except ReflinkError as error:
        print(f'reflink_copy: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
