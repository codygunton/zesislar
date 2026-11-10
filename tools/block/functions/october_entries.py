"""Render FP301-shaped entry modules from a function's checked block entries.

Use this when the FP-20261101 forward pass cannot render a function (a call
or an undesigned loop). Each block keeps its checked source entry unchanged.
The adapter adds only:

  fp_machineAt<suffix> args returnAddress K :=
    ((∃ <the entry's binders after args>, <entry> args <binders>) ∗ K)

and the data-only registrations that FP301 Structural modules carry: one
unfold marker and one introduction per definition, proved by reflexivity.
The source body is copied byte for byte into its introduction. No proof
script is written. The output RESULT.json has the case shape that
render_function_callers.py reads.

With --expand-pure NAME the wrapper holds a convertible copy of the source
entry body in which each application of the definition NAME (applied to
exactly its own parameter names) is replaced by its body. NAME is a pure
definition or an iProp helper. This states the entry in the flat shape of
rendered entries: owned atoms and top-level conjuncts (F44: a link is a
separate pure conjunct). The source entry is not changed.

Usage: october_entries.py --function NAME --output RESULT_DIR [--expand-pure NAME]...
"""
from pathlib import Path
import argparse, hashlib, json, re, sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/block'))
from function_profiles import load_profile

HEADER = ('Require ZesuSsz.Automation.Hooks.\n'
          'Require Import isla.riscv64.riscv64.\n'
          'From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.\n'
          'Require Import stdpp.bitvector.definitions.\n')
INTRO = '@ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma'
PROOF = ' := @PreOrder_Reflexive _ _ bi.entails_po _.\n'
CONTEXT = '`{!islaG Sigma} `{!threadG}'


def bind(path):
    path = Path(path)
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def definition(source, name):
    """Return (binder groups, body) of one `Definition name ... : iProp Sigma := body.`"""
    match = re.search(r'^Definition ' + re.escape(name) + r' ' + re.escape(CONTEXT)
                      + r'\s*(?P<telescope>(?:\s*\([^()]*\))*)\s*:\s*iProp Sigma :=\n(?P<body>.*?\)%I)\.\n',
                      source, re.S | re.M)
    if match is None:
        raise ValueError('The source definition is absent or has another shape: ' + name)
    groups = []
    for names, kind in re.findall(r'\(([^():]+):\s*([^()]+)\)', match['telescope']):
        groups.append((names.split(), kind.strip()))
    if len(groups) != match['telescope'].count('('):
        raise ValueError('The source telescope is not a list of typed groups: ' + name)
    return groups, match['body']


def pure_definition(source, name):
    """Return (parameter names, body) of `Definition name (groups) : Prop := body.`
    (or an iProp helper with the islaG context)."""
    match = re.search(r'^Definition ' + re.escape(name) + r'(?: ' + re.escape(CONTEXT) + r')?'
                      r'(?P<telescope>(?:\s*\([^()]*\))*)\s*:\s*(?:Prop|iProp Sigma) :=\n'
                      r'(?P<body>.*?)\.\n', source, re.S | re.M)
    if match is None:
        raise ValueError('The pure definition is absent or has another shape: ' + name)
    names = [n for group, _ in re.findall(r'\(([^():]+):\s*([^()]+)\)', match['telescope'])
             for n in group.split()]
    return names, match['body']


def expand(body, name, parameters, definition_body):
    """Replace `name <parameters>` in body by the definition body (same names, so no renaming)."""
    application = name + ' ' + ' '.join(parameters)
    count = body.count(application)
    if count != 1 or len(re.findall(r'\b' + re.escape(name) + r'\b', body)) != 1:
        raise ValueError('The entry applies ' + name + ' other than once to its own parameter names.')
    inner = definition_body.strip()
    head = re.match(r'(let \w+ := [^\n]+ in)\n', inner)
    if head:
        if not body.lstrip().startswith(head[1]):
            raise ValueError('The pure definition binds a let that the entry does not bind.')
        inner = inner[head.end():]
    return body.replace(application, '(' + inner.strip() + ')')


def telescope(groups):
    return ' '.join('(' + ' '.join(names) + ' : ' + kind + ')' for names, kind in groups)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--function', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--expand-pure', action='append', default=[])
    options = parser.parse_args()
    profile = load_profile(options.function)
    spec = profile['entry_source']
    source_path = ROOT / spec['file']
    source = source_path.read_text()
    module = '.'.join(Path(spec['file']).with_suffix('').parts)
    output = options.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    directory = ROOT / profile.generated_directory
    directory.mkdir(parents=True, exist_ok=True)
    imports = ''.join(line + '\n' for line in profile['contract_requires'])

    # The helper predicates get one unfold marker each, in one module that
    # every Structural module exports, as the source function's own
    # registrations declare them (selected code excluded: it stays transparent).
    helpers = ['(* Unfold markers for the shared helpers of ' + module + '. No proof script. *)\n',
               HEADER, imports, 'Local Open Scope Z_scope.\n']
    for name in spec['helpers']:
        definition(source, name)
        helpers.append('#[export] Instance ' + name + '_unfold : LithiumUnfold (@' + name + ') := I.\n'
                       '#[export] Typeclasses Opaque ' + name + '.\n')
    helper_path = directory / 'EntryHelpers.v'
    helper_path.write_text(''.join(helpers))
    helper_module = profile.qualified('EntryHelpers')

    cases = []
    for suffix in profile['blocks']:
        name = spec['definition_prefix'] + suffix
        groups, body = definition(source, name)
        (first, first_kind), rest = groups[0], groups[1:]
        if first_kind != profile.args_type or len(first) != 1:
            raise ValueError('The first source binder is not the argument record: ' + name)
        parameter = first[0]
        binders = [name for names, _ in rest for name in names]
        target = 'fp_machineAt' + suffix
        closed = ('((∃ ' + telescope(rest) + ', ' + module + '.' + name + ' (args) '
                  + ' '.join(binders) + ') ∗ K)%I')
        record_parameter = 'args'
        expanded = []
        for pure in options.expand_pure:
            if re.search(r'\b' + re.escape(pure) + r'\b', body):
                body = expand(body, pure, *pure_definition(source, pure))
                expanded.append(pure)
        if expanded:
            # The wrapper states a convertible copy of the entry body; its record
            # parameter keeps the source name so the copied body needs no renaming.
            record_parameter = parameter
            closed = '((∃ ' + telescope(rest) + ', (' + body + ')) ∗ K)%I'
        entries = (
            '(* Rendered from the checked entry ' + module + '.' + name + '.\n'
            + ('   Only the existential closure of its binders and the continuation K are added. No proof script. *)\n'
               if not expanded else
               '   A convertible copy of its body with ' + ', '.join(expanded) + ' unfolded in place, closed\n'
               '   existentially over its binders, with the continuation K. No proof script. *)\n')
            + HEADER + imports + 'Local Open Scope Z_scope.\n'
            'Definition ' + target + ' ' + CONTEXT + ' (' + record_parameter + ' : ' + profile.args_type
            + ') (returnAddress : Z) (K : iProp Sigma) : iProp Sigma := ' + closed + '.\n')
        structural = (
            '(* Rendered from the checked entry ' + module + '.' + name + '. No proof script. *)\n'
            + HEADER + imports + 'Local Open Scope Z_scope.\n'
            'Require Export ' + helper_module + '.\n'
            'Require Import ' + profile.qualified('Pilot' + suffix + 'Entries') + '.\n'
            '#[export] Instance ' + target + '_unfold : LithiumUnfold (@' + target + ') := I.\n'
            '#[export] Typeclasses Opaque ' + target + '.\n'
            '#[export] Instance ' + target + '_intro ' + CONTEXT + ' (' + record_parameter + ' : '
            + profile.args_type + ') (returnAddress : Z) (K : iProp Sigma) :\n  ' + INTRO + ' (' + target
            + ' (' + record_parameter + ') (returnAddress) (K))\n  ' + closed + PROOF + '\n'
            '#[export] Instance ' + name + '_unfold : LithiumUnfold (@' + module + '.' + name + ') := I.\n'
            '#[export] Typeclasses Opaque ' + module + '.' + name + '.\n'
            '#[export] Instance ' + name + '_intro ' + CONTEXT + ' ' + telescope(groups) + ' :\n  '
            + INTRO + ' (' + module + '.' + name + ' ' + parameter + ' ' + ' '.join(binders) + ')\n  ('
            + body + ')' + PROOF)
        entries_path = directory / ('Pilot' + suffix + 'Entries.v')
        structural_path = directory / ('Pilot' + suffix + 'Structural.v')
        entries_path.write_text(entries)
        structural_path.write_text(structural)
        cases.append({'pc': profile.pc(suffix), 'status': 'source_declarations_rendered',
                      'source': {'file': str(source_path), 'definition': name},
                      'binders': binders, 'expanded_pure_definitions': expanded, 'entries': bind(entries_path), 'structural': bind(structural_path),
                      'proof_ran': False})
    result = {'status': 'SOURCE_DECLARATIONS_ONLY', 'function': profile.name,
              'origin': 'checked source block entries (not the FP-20261101 forward pass)',
              'source': bind(source_path), 'profile': bind(profile.path), 'helpers': bind(helper_path),
              'generator': bind(Path(__file__)), 'cases': cases}
    (output / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'rendered': len(cases)}))


if __name__ == '__main__':
    main()
