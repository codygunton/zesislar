"""Locate only an exact aggregate under the shared memory parent."""
import os, re
from pathlib import Path
CGROUP_ROOT=Path("/sys/fs/cgroup")

def aggregate_root(environment=os.environ, proc=Path('/proc'), root=CGROUP_ROOT):
    name = environment.get('ZESU_AGGREGATE_SLICE', '')
    if not environment.get('ZESU_IN_BATCH') or not re.fullmatch(r'zesuworkloads-aggregate[0-9]+p[0-9]+r[0-9]+\.slice', name):
        raise ValueError('Execution requires one fresh stock batch per attempt.')
    membership = next(line[3:] for line in (proc/'self/cgroup').read_text().splitlines() if line.startswith('0::'))
    parts = Path(membership).parts
    if parts.count(name) != 1:
        raise ValueError('The attempt does not belong to its stock aggregate.')
    selected = root/Path(*parts[1:parts.index(name)+1])
    if selected.parent.name != 'zesuworkloads.slice':
        raise ValueError('The stock aggregate is outside the shared workload parent.')
    if ((selected.parent/'memory.max').read_text().strip() != '187904819200' or
            (selected.parent/'memory.swap.max').read_text().strip() != '0'):
        raise ValueError('The shared workload parent lacks its exact memory fence.')
    if not (selected/'cpu.stat').is_file():
        raise ValueError('The stock aggregate has no CPU counter.')
    return selected
