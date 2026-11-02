"""Select DAG weights from existing authenticated physical compiler receipts."""
from pathlib import Path

from entry_chain import binding, read_bound
from object_imports import _record


GIB = 1024 ** 3
# Preserve the existing unmeasured compiler reservation for every source class.
CLASS_DEFAULTS = {'generated': 16 * GIB, 'automation': 16 * GIB, 'library': 16 * GIB}


def source_class(module):
    if '.Generated.' in module:
        return 'generated'
    if '.Automation.' in module:
        return 'automation'
    return 'library'


def weights(ordered, modules, workspace, compiler, flags, profile=None):
    """A missing or mismatched measurement retains its full class default."""
    workspace = Path(workspace).resolve()
    selected = {}
    if profile is not None:
        value = read_bound(profile)
        if (not isinstance(value, dict) or set(value) != {'schema', 'modules'} or
                value['schema'] != 'entry-chain.declaration-resources.v1' or
                not isinstance(value['modules'], list)):
            raise ValueError('The declaration resource profile is unsupported.')
        for row in value['modules']:
            if (not isinstance(row, dict) or set(row) != {'module', 'receipt'} or
                    row['module'] not in ordered or row['module'] in selected):
                raise ValueError('The declaration resource profile names another module.')
            # A changed profile binding must refuse before any class fallback.
            selected[row['module']] = (row['receipt'], read_bound(row['receipt']))
    result, evidence = {}, {}
    for module in ordered:
        category = source_class(module)
        result[module] = CLASS_DEFAULTS[category]
        evidence[module] = {'class': category, 'reason': 'unmeasured_class_default'}
        if module not in selected:
            continue
        reference, receipt = selected[module]
        try:
            source = workspace / modules[module]
            _record(reference, module, source, Path(receipt['object']['path']), compiler,
                    flags, workspace)
            physical = read_bound(receipt['physical_result'])
            peak = physical.get('peak_rss_KiB')
            if type(peak) is not int or peak <= 0:
                raise ValueError('The completed physical compiler lacks its positive peak.')
        except (KeyError, OSError, TypeError, ValueError) as error:
            evidence[module].update(reason='unmatched_measurement', detail=str(error), receipt=reference)
            continue
        result[module] = max(GIB, (peak * 1024 * 3 + 1) // 2)
        evidence[module] = {'class': category, 'reason': 'completed_matching_measurement',
                            'receipt': reference, 'physical_result': receipt['physical_result'],
                            'peak_bytes': peak * 1024}
    return {'weights': result, 'evidence': evidence, 'profile': profile,
            'qualification': 'Measurements bind source, compiler, and flags. Changed imports can change memory use.'}
