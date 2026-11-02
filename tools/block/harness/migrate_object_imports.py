#!/usr/bin/env python3
"""Inspect accepted objects without proof search or Rocq compilation."""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path[:0] = [str(HERE / 'code'), str(HERE.parent)]

from object_import_migration import main


if __name__ == '__main__':
    main()
