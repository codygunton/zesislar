#!/usr/bin/env python3
"""Write the stepping-only variant of generated callers (a diagnostic probe; never commit its output).

usage: probe_mirror.py --output-dir DIR [--root TREE] Caller.v ...

For each caller, writes DIR/<caller directory name>/Probe<case>.v: the caller with every generated
entry it names (its precondition and each successor) replaced by a local copy that keeps the
generated structure (one
definition per entry class, `(class [∨ class ...]) ∗ K`, the same LithiumUnfold / Typeclasses Opaque /
ZesuPureFactIntro registrations the generated *Structural.v files give) and deletes pure facts:
the precondition keeps only its function-domain facts and list lengths, successors state no pure
fact. The rules then see what they see in the generated caller, minus the history, so the probe
tells whether a block's cost or failure comes from stepping or from its facts.
The entry modules are read from TREE (default: this worktree). The probe drops the caller's imports
of the generated Entries/Structural modules (it inlines its own copies) and of the residual-lemma
hints (ZesuSsz.Residuals.*, ZesuSsz.Compliance.DecodeItemMeaningPorted: they match the deleted
facts). The proof script is the caller's own. Prototype:
_build/agents/researcher/survey/gen_mirror.py (variant t0s).
"""
import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
BINDERS = re.compile(r'∃ ((?:\((?:[^()]|\([^()]*\))*\) ?)+),')
BINDER = re.compile(r'\((\w+) : ((?:[^()]|\([^()]*\))*)\)')
ENTRY_USE = re.compile(r'\((ZesuSsz\.Generated\.[\w.]+)\.(\w+) (\(?args\)?) (\(?returnAddress\)?) (\(?K\)?)\)')
# A sealed caller's Edges<case> module holds history instances: the probe deletes the history facts.
DROPPED_IMPORT = re.compile(r'Require Import (ZesuSsz\.Generated\.\w+\.FP301\.(\w+(Entries|Structural)|Edges\w*)\.'
                            r'|ZesuSsz\.Residuals\.|ZesuSsz\.Compliance\.DecodeItemMeaningPorted\.)')
LENGTH_FACT = re.compile(r'^\(*List\.length (\w+|\(\w+ \(?\w+\)?\)) = \d+\)?(%nat)?\)*$')


def read_def(path, name):
    """The text of `Definition name ...` up to the next Definition, whitespace collapsed."""
    text = Path(path).read_text()
    start = text.index('Definition ' + name + ' ')
    end = text.find('\nDefinition ', start + 10)
    return re.sub(r'\s+', ' ', text[start:end if end > 0 else len(text)]).strip()


def strip_outer(text):
    """text without the brackets that enclose all of it."""
    text = text.strip()
    while text.startswith('(') and text.endswith(')'):
        depth = 0
        for index, char in enumerate(text):
            if char in '([':
                depth += 1
            elif char in ')]':
                depth -= 1
                if depth == 0:
                    break
        if index != len(text) - 1:
            break
        text = text[1:-1].strip()
    return text


def split_top(text):
    """Split at each top-level separating conjunction `∗` (not the one of `↦ₘ{DfracOwn 1}∗`)."""
    parts, depth, current, previous = [], 0, '', ''
    for char in text:
        if char in '([':
            depth += 1
        elif char in ')]':
            depth -= 1
        if depth == 0 and char == '∗' and previous != 'ₘ' and not re.search(r'↦ₘ\{[^{}]*\}$', current):
            parts.append(current.strip())
            current, previous = '', char
            continue
        current += char
        if not char.isspace():
            previous = char
    if current.strip():
        parts.append(current.strip())
    return parts


def split_and(text):
    """Split at each top-level `/\\`."""
    parts, depth, current, index = [], 0, '', 0
    while index < len(text):
        char = text[index]
        if char in '([':
            depth += 1
        elif char in ')]':
            depth -= 1
        if depth == 0 and text.startswith('/\\', index):
            parts.append(current.strip())
            current, index = '', index + 2
            continue
        current += char
        index += 1
    parts.append(current.strip())
    return parts


def module_path(root, module):
    return Path(root) / (module.replace('.', '/') + '.v')


def class_defs(root, module, name):
    """[(class name, body)] of an entry: its classes `c args returnAddress [∨ ...]`, or itself."""
    path = module_path(root, module)
    text = read_def(path, name)
    text = text[text.index(':= ') + 3:]
    text = text[:text.index('%I.') + 3]
    match = re.fullmatch(r'\(\(?((?:\w+ \(?args\)? \(?returnAddress\)?(?: ∨ )?)+)\)? ∗ K\)%I\.', text)
    if match:
        out = []
        for class_name in re.findall(r'(\w+) \(?args\)? \(?returnAddress\)?', match.group(1)):
            body = read_def(path, class_name)
            body = body[body.index(':= ') + 3:]
            if not body.endswith('%I.'):
                raise SystemExit('probe_mirror: %s: %s does not end in %%I.' % (path, class_name))
            out.append((class_name, body[:-3].strip()))
        return out
    match = re.fullmatch(r'\((\(∃ .*\)) ∗ K\)%I\.', text)
    if not match:
        raise SystemExit('probe_mirror: %s: entry %s has an unknown shape' % (path, name))
    return [(name, match.group(1))]


def is_domain(fact, binders):
    """A precondition fact the probe keeps: it names no entry binder and is a domain fact (mentions
    the return address, or no bit-vector, list element or decision), or it is a list length."""
    names = set(re.findall(r'\b[A-Za-z_]\w*\b', fact))
    domain = not (names & binders) and ('eturnAddress' in fact or not re.search(r'bv_|List\.nth|bool_decide', fact))
    return domain or LENGTH_FACT.search(fact) is not None


def prune(body, keep, stats):
    """body `(∃ binders, X)` or `(X)` without the pure facts `keep(fact, binder names)` rejects."""
    if not (body.startswith('(') and body.endswith(')')):
        raise SystemExit('probe_mirror: entry body is not bracketed: %s' % body[:80])
    inner = body[1:-1].strip()
    match = BINDERS.match(inner)
    prefix, binders = '', set()
    if match:
        prefix = match.group(0) + ' '
        binders = {name for name, _ in BINDER.findall(match.group(1))}
        inner = inner[match.end():].strip()

    def walk(part):
        part = part.strip()
        if part.startswith('⌜') and part.endswith('⌝'):
            fact = strip_outer(part[1:-1])
            facts = [fact] if re.match(r'∃|forall|∀', fact) else split_and(fact)
            kept = [fact for fact in facts if keep(fact, binders)]
            stats['pure'] += len(facts)
            stats['kept'] += len(kept)
            return '⌜' + ' /\\ '.join('(%s)' % fact for fact in kept) + '⌝' if kept else None
        if part.startswith('('):
            pieces = split_top(strip_outer(part))
            if len(pieces) > 1:
                kept = [piece for piece in map(walk, pieces) if piece is not None]
                return '(' + ' ∗ '.join(kept) + ')' if kept else None
        return part

    parts = split_top(strip_outer(inner)) if len(split_top(inner)) == 1 else split_top(inner)
    kept = [part for part in map(walk, parts) if part is not None]
    return '(' + prefix + '(' + (' ∗ '.join(kept) or 'True') + '))'


def registrations(name, signature, body):
    return '''#[export] Instance {n}_unfold : LithiumUnfold (@{n}) := I.
#[export] Typeclasses Opaque {n}.
#[export] Instance {n}_intro {s} :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma ({n} (args) (returnAddress){k})
  {b}%I := @PreOrder_Reflexive _ _ bi.entails_po _.
'''.format(n=name, s=signature, b=body, k=' (K)' if '(K : iProp Sigma)' in signature else '')


def mirror(caller, root=ROOT):
    """(probe text, {entry key: [(class, pure facts, kept)]}) of one caller file."""
    source = Path(caller).read_text()
    head = source[:source.index('Definition DesignedEntry')]
    statement = source[source.index('Definition DesignedEntry'):source.index('Proof.')]
    proof = source[source.index('Proof.'):]
    imports = '\n'.join(line for line in head.splitlines() if not DROPPED_IMPORT.match(line)) + '\n'
    entries = {}

    def local_use(match):
        key = 'pre' if not entries else 'succ%d' % (len(entries) - 1)
        entries[key] = (match.group(1), match.group(2))
        return '(%s_P %s %s %s)' % (key, match.group(3), match.group(4), match.group(5))

    statement = ENTRY_USE.sub(local_use, statement)
    if 'pre' not in entries or 'ZesuSsz.Generated' in statement:
        raise SystemExit('probe_mirror: %s: entry uses not recognised' % caller)
    argument_type = re.search(r'\(args : (\w+)\)', statement).group(1)
    requires = []
    for module, _ in entries.values():
        for line in module_path(root, module).read_text().splitlines():
            if line.startswith('Require') and line not in requires:
                requires.append(line)
    signature = '`{!islaG Sigma} `{!threadG} (args : %s) (returnAddress : Z)' % argument_type
    definitions, stats = [], {}
    for key, (module, name) in entries.items():
        names, stats[key] = [], []
        for index, (class_name, body) in enumerate(class_defs(root, module, name)):
            counts = {'pure': 0, 'kept': 0}
            keep = is_domain if key == 'pre' else (lambda fact, binders: False)
            pruned = prune(body, keep, counts)
            local = '%s_c%d' % (key, index)
            names.append(local)
            stats[key].append((class_name, counts['pure'], counts['kept']))
            definitions.append('Definition %s %s : iProp Sigma := %s%%I.\n' % (local, signature, pruned)
                               + registrations(local, signature, pruned))
        classes = ('%s (args) (returnAddress)' % names[0] if len(names) == 1
                   else '(' + ' ∨ '.join('%s args returnAddress' % local for local in names) + ')')
        wrapped = '(%s ∗ K)' % classes
        definitions.append('Definition %s_P %s (K : iProp Sigma) : iProp Sigma := %s%%I.\n'
                           % (key, signature, wrapped)
                           + registrations('%s_P' % key, signature + ' (K : iProp Sigma)', wrapped))
    text = '\n'.join(requires) + '\n' + imports + '\n' + '\n'.join(definitions) + '\n' + statement + proof
    return text, stats


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('callers', type=Path, nargs='+')
    options = parser.parse_args(argv)
    options.output_dir.mkdir(parents=True, exist_ok=True)
    for caller in options.callers:
        case = re.search(r'Caller(\w+)\.v$', caller.name)
        if not case:
            raise SystemExit('probe_mirror: %s is not a Caller<case>.v' % caller)
        text, stats = mirror(caller, options.root)
        output = options.output_dir / caller.resolve().parent.name / ('Probe%s.v' % case.group(1))
        output.parent.mkdir(exist_ok=True)
        output.write_text(text)
        print('%s %s' % (output, ' '.join('%s:%s' % (key, ','.join('%d/%d' % (kept, pure) for _, pure, kept in rows))
                                           for key, rows in stats.items())))
    return 0


if __name__ == '__main__':
    sys.exit(main())
