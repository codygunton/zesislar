"""Derive unit data from authentic tracked inputs. Never admission evidence."""
import json
from pathlib import Path
import sys

SOURCE_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(SOURCE_ROOT / 'tools/block/harness'))
import _historical_fixtures as historical

_ROOT = None


def repository():
    global _ROOT
    if _ROOT is None:
        historical.prepare()
        _ROOT = historical.root() / 'repository'
        evidence = SOURCE_ROOT / 'ZesuSsz/Evidence'
        sources = [source for source in evidence.iterdir()
               if source.suffix in ('.v', '.json', '.txt')]
        for directory in ['route_repair', 'array_store', 'precommitment', 'i75']:
            sources.extend((evidence / directory).rglob('*'))
        for source in sorted(sources):
            if not source.is_file():
                continue
            target = _ROOT / source.relative_to(SOURCE_ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            if source.suffix == '.json':
                target.write_text(json.dumps(historical.read_json(source), indent=2) + '\n')
            else:
                target.write_bytes(source.read_bytes())
    return _ROOT
