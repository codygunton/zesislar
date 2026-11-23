"""Proved functions are black boxes (ZesuSsz/Contracts/proved_functions.json).

Fails the gate when:
(a) a caller module -- another function's generated entries or callers, an
    Automation2 module, or another function's Compliance module -- requires an
    internal module of a registered function instead of its interface;
    A `legacy_callers` row needs a reason; beyond the grandfathered frozen-core
    nextUint64 rows, only a frozen ZesuSsz/Automation/ module or a frozen
    class-R module (hygiene baseline legacy_entry_files) may be listed;
(c) a function profile's call to a registered black box does not name the
    interface's public spec (call_boundary.interface_of, which the block
    generator applies to every call it renders);
(d) a `*Compliance` theorem in ZesuSsz/Compliance has no registry entry, or a
    generated interface module is not a fresh render of the registry.
(b), unfolding a sealed name outside its interface, is in
ZesuSsz/Evidence/check_proof_hygiene.py, which scans every `.v` file.
"""
from pathlib import Path
import json, re, sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/block'))
from call_boundary import CallRefused, interface_of
from render_interfaces import stale

REQUIRE = re.compile(r'(?:\bFrom\s+(\S+)\s+)?\bRequire\s+(?:(?:Import|Export)\s+)?(.*?)\.(?=\s|$)', re.S)
# Legacy callers admitted before the admission rule below (2026-11-14 ruling): frozen-core nextUint64
# Compliance modules, kept until they retire. No row may join this set.
GRANDFATHERED_LEGACY = frozenset({
    ('ZesuSsz/Compliance/NextUint64ExitMeanings.v', 'ZesuSsz.Compliance.DecodeItemReturnRestorationFacts'),
    ('ZesuSsz/Compliance/NextUint64CallBridge.v', 'ZesuSsz.Contracts.DecodeItemCompositional'),
    ('ZesuSsz/Compliance/NextUint64CallBridge.v', 'ZesuSsz.Compliance.DecodeItemCompositionalCompliance'),
})


def frozen_class_r(root=ROOT):
    """The frozen class-R modules: the hygiene baseline's approved AllLegacy entry files."""
    baseline = Path(root) / 'ZesuSsz/Evidence/hygiene_baseline.json'
    return set(json.loads(baseline.read_text())['legacy_entry_files']) if baseline.exists() else set()


def legacy_admission_violations(registry, root=ROOT):
    """A `legacy_callers` row needs a reason, and a new row is admitted only for a module under the
    frozen ZesuSsz/Automation/ core or a frozen class-R module."""
    class_r = frozen_class_r(root)
    errors = []
    for entry in registry['functions']:
        for row in entry.get('legacy_callers', []):
            if not row.get('reason', '').strip():
                errors.append('%s: legacy caller %s lists no reason' % (entry['function'], row['path']))
            if ((row['path'], row['module']) not in GRANDFATHERED_LEGACY
                    and not row['path'].startswith('ZesuSsz/Automation/') and row['path'] not in class_r):
                errors.append('%s: new legacy caller %s (%s) refused: only a frozen ZesuSsz/Automation/ module '
                              'or a frozen class-R module may be listed; import %s'
                              % (entry['function'], row['path'], row['module'],
                                 (entry.get('interface') or {}).get('module')))
    return errors

THEOREM = re.compile(r'^\s*(?:Theorem|Lemma)\s+(\w*Compliance)\b', re.M)


def code_of(text):
    """The text with comments removed (nested), keeping line breaks."""
    out, depth, index = [], 0, 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == '(*':
            depth, index = depth + 1, index + 2
        elif pair == '*)' and depth:
            depth, index = depth - 1, index + 2
        else:
            out.append(text[index] if not depth or text[index] == '\n' else ' ')
            index += 1
    return ''.join(out)


def required_modules(text):
    modules = []
    for match in REQUIRE.finditer(code_of(text)):
        prefix, names = match.groups()
        for name in names.split():
            modules.append(prefix + '.' + name if prefix else name)
    return modules


def module_of(path):
    """The logical module of a ZesuSsz source path."""
    return 'ZesuSsz.' + str(path)[len('ZesuSsz/'):-len('.v')].replace('/', '.')


def internal_modules(entry, root=ROOT):
    """The modules a caller must not require: the function's own modules, except the
    modules its interfaces re-export and the interfaces themselves."""
    interface = entry['interface']
    public = set(interface['exports']) | set(interface['correct']['exports'])
    result = set()
    for path in sorted((Path(root) / 'ZesuSsz').rglob('*.v')):
        relative = str(path.relative_to(root))
        if relative.startswith(tuple(entry['owned_prefixes'])):
            module = module_of(relative)
            if module not in public:
                result.add(module)
    return result


def caller_scopes(entry, root=ROOT):
    """Source files that are callers of `entry` in the sense of rule (a)."""
    owned = tuple(entry['owned_prefixes'])
    files = []
    for profile in sorted((Path(root) / 'tools/block/functions').glob('*.json')):
        data = json.loads(profile.read_text())
        if data.get('function') == entry['function']:
            continue
        for key in ('generated_directory', 'callers_directory'):
            directory = data.get(key)
            if directory:
                files += sorted((Path(root) / directory).rglob('*.v'))
    files += sorted((Path(root) / 'ZesuSsz/Automation2').rglob('*.v'))
    files += [path for path in sorted((Path(root) / 'ZesuSsz/Compliance').rglob('*.v'))
              if not str(path.relative_to(root)).startswith(owned)]
    return sorted(set(files))


def import_violations(registry, root=ROOT):
    errors = []
    for entry in registry['functions']:
        if not entry.get('interface'):
            continue
        internal = internal_modules(entry, root)
        # A legacy caller is listed with its reason; a listed import that is gone fails too.
        legacy = {(row['path'], row['module']) for row in entry.get('legacy_callers', [])}
        seen = set()
        for path in caller_scopes(entry, root):
            relative = str(path.relative_to(root))
            for module in required_modules(path.read_text()):
                if (relative, module) in legacy:
                    seen.add((relative, module))
                elif module in internal:
                    errors.append('%s: requires %s, an internal module of the proved function %s; import %s'
                                  % (relative, module, entry['function'], entry['interface']['module']))
        errors += ['%s: listed legacy caller no longer requires %s; remove it from the registry' % row
                   for row in sorted(legacy - seen)]
    return errors


def call_violations(registry, root=ROOT):
    errors = []
    for profile in sorted((Path(root) / 'tools/block/functions').glob('*.json')):
        for call in json.loads(profile.read_text()).get('calls', []):
            try:
                interface_of(call, registry)
            except CallRefused as error:
                errors.append('%s: call at %s: %s' % (profile.relative_to(root), call.get('call_site_pc'), error))
    return errors


def premise_violations(entry, root=ROOT):
    """An `assumed` row without an interface is a trusted runtime premise: `premise` names the module,
    the premise (`□ instr_pre <entry> <call spec>`) and the call spec, and the module defines both."""
    if entry['status'] != 'assumed' or entry.get('interface'):
        return []
    premise = entry.get('premise') or {}
    if sorted(premise) != ['call_spec', 'module', 'name']:
        return ['%s: an assumed row without an interface names premise {module, name, call_spec}'
                % entry['function']]
    path = Path(root) / ('ZesuSsz/' + premise['module'][len('ZesuSsz.'):].replace('.', '/') + '.v')
    if not premise['module'].startswith('ZesuSsz.') or not path.exists():
        return ['%s: premise module %s does not exist' % (entry['function'], premise['module'])]
    text = code_of(path.read_text())
    return ['%s: %s does not define %s' % (entry['function'], premise['module'], name)
            for name in (premise['name'], premise['call_spec'])
            if not re.search(r'\bDefinition\s+%s\b' % re.escape(name), text)]


def coverage_violations(registry, root=ROOT):
    owned = {name for entry in registry['functions'] for name in entry['compliance_theorems']}
    errors = []
    for path in sorted((Path(root) / 'ZesuSsz/Compliance').rglob('*.v')):
        for name in THEOREM.findall(code_of(path.read_text())):
            if name not in owned:
                errors.append('%s: compliance theorem %s has no entry in ZesuSsz/Contracts/proved_functions.json'
                              % (path.relative_to(root), name))
    for entry in registry['functions']:
        if entry.get('interface') and entry['status'] not in ('proved', 'assumed'):
            errors.append('%s: only a proved or assumed function has an interface' % entry['function'])
        if entry['status'] == 'proved' and not entry['compliance_theorems']:
            errors.append('%s: a proved function names its compliance theorems' % entry['function'])
        errors += premise_violations(entry, root)
    return errors


def violations(root=ROOT):
    registry = json.loads((Path(root) / 'ZesuSsz/Contracts/proved_functions.json').read_text())
    errors = (import_violations(registry, root) + legacy_admission_violations(registry, root)
              + call_violations(registry, root) + coverage_violations(registry, root))
    errors += ['interface module not fresh (run tools/block/render_interfaces.py): ' + path
               for path in stale(registry)]
    return errors


def main():
    errors = violations()
    for error in errors:
        print(error)
    if not errors:
        print('Proved functions are black boxes: registry, interfaces, imports and calls agree.')
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
