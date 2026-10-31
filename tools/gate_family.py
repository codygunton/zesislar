"""Use reviewed measurements as admission predictions for stock gate families."""
from pathlib import Path
import hashlib
import json

from module_memory import measurement_claim

ROOT = Path(__file__).resolve().parent
PROFILE = ROOT / 'gate-families.json'


def select(target, command, physical_fence_bytes, *, profile=PROFILE):
    value = json.loads(Path(profile).read_text())
    if (set(value) != {'schema', 'families'}
            or value['schema'] != 'zesu.reviewed-gate-families.v1'
            or not isinstance(value['families'], dict)):
        raise ValueError('The reviewed gate-family profile is invalid.')
    row = value['families'].get(target)
    if row is None:
        return None
    if (set(row) != {'command', 'physical_fence_bytes', 'measurement', 'peak_bytes', 'authority'}
            or type(row['physical_fence_bytes']) is not int
            or type(row['peak_bytes']) is not int or row['peak_bytes'] <= 0):
        raise ValueError('The reviewed gate-family row is invalid.')
    if command != row['command'] or physical_fence_bytes != row['physical_fence_bytes']:
        return None
    binding = row['measurement']
    if not isinstance(binding, dict) or set(binding) != {'path', 'sha256'}:
        raise ValueError('The reviewed gate measurement lacks its binding.')
    relative = Path(binding['path'])
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('The reviewed gate measurement path is not contained.')
    path = (Path(profile).parent / relative).resolve()
    if not path.is_relative_to(Path(profile).parent.resolve()):
        raise ValueError('The reviewed gate measurement leaves its profile root.')
    payload = path.read_bytes()
    if hashlib.sha256(payload).hexdigest() != binding['sha256']:
        raise ValueError('The reviewed gate measurement changed.')
    measurement = json.loads(payload)
    if (measurement.get('target') != target or measurement.get('success') is not True
            or type(measurement.get('exit_code')) is not int or measurement['exit_code'] != 0
            or type(measurement.get('completed_ns')) is not int or measurement['completed_ns'] <= 0
            or measurement.get('aggregate_peak_bytes') != row['peak_bytes']
            or measurement.get('measurement_scope') != 'Complete owned stock aggregate before guard cleanup.'):
        raise ValueError('The reviewed gate measurement is incomplete or names another family.')
    return {'reason': 'reviewed_completed_gate_family_peak', 'family': target,
            'measurement': {'path': str(path), 'sha256': binding['sha256']},
            'measurement_provenance': measurement.get('cache_provenance'),
            'aggregate_peak_bytes': row['peak_bytes'], 'authority': row['authority'],
            'claim_bytes': measurement_claim(physical_fence_bytes, row['peak_bytes'],
                                             completed=True, matching=True),
            'physical_fence_bytes': physical_fence_bytes,
            'qualification': 'Admission prediction from a reviewed completed family measurement. '
                             'This is not an uncached-build claim. Source changes can increase memory use. '
                             'The physical fence and shared backstop remain mandatory.'}
