#!/usr/bin/env python3
"""Assemble the shared ported meaning module by verbatim copy.

Each source file's body (everything after its import block) is copied byte for
byte into its own `Module` section; the import lines are merged at the top,
without the frozen umbrella `ZesuSsz.Automation.All`. A source can be cut at a
named top-level command (the copy stops before it). Nothing is rewritten.
Usage: port_meaning_lemmas.py WORKTREE OUTPUT.v"""
import re, sys, hashlib, json
from pathlib import Path

W = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2])
# (source, module name, stop before this top-level command name or None)
SOURCES = [
    ('ZesuSsz/Contracts/RlpDecodeItemReturnImages.v', 'PortedReturnImages', None),
    ('ZesuSsz/Compliance/DecodeItemSemanticIntroduction.v', 'PortedSemanticIntroduction', None),
    ('ZesuSsz/Compliance/DecodeItemSailEvaluation.v', 'PortedSailEvaluation', None),
    ('ZesuSsz/Compliance/DecodeItemSailIntroduction.v', 'PortedSailIntroduction', 'decodeItemLongCandidateFromProvenance'),
    ('ZesuSsz/Compliance/DecodeItemPathAgreement.v', 'PortedPathAgreement', None),
    ('ZesuSsz/Compliance/DecodeItemReturnExitResources.v', 'PortedReturnExitResources', None),
    ('ZesuSsz/Compliance/DecodeItemReturnExitPure.v', 'PortedReturnExitPure', None),
]
DROP = {'Require Import ZesuSsz.Automation.All.',
        # Needed only by the long-class lemmas after the SailIntroduction cut.
        'Require Import ZesuSsz.Compliance.DecodeItemSailFold.',
        'Require Import ZesuSsz.Compliance.ByteFold.'}
IMPORT = re.compile(r'^(Require|From \S+ Require)\b')
FROZEN_ALL = 'Require Import ZesuSsz.Automation.All.'
import os
FROZEN_SUBSTITUTE = os.environ.get('PORT_FROZEN_SUBSTITUTE', 'Import ZesuSsz.Automation.Hooks.')
replaced = {'ZesuSsz.' + rel[len('ZesuSsz/'):-2].replace('/', '.'): name for rel, name, _ in SOURCES}

requires, bodies, manifest = [], [], []
for rel, name, stop in SOURCES:
    text = (W / rel).read_text()
    own, body = [], []
    for line in text.split('\n'):
        if IMPORT.match(line):
            if line == FROZEN_ALL and FROZEN_SUBSTITUTE:
                # The copied proofs were checked under the frozen core's `lia`
                # and `bv_solve`; import only the frozen Hooks module that owns them.
                own.append(FROZEN_SUBSTITUTE)
                if 'Require ZesuSsz.Automation.Hooks.' not in requires:
                    requires.append('Require ZesuSsz.Automation.Hooks.')
                continue
            if line in DROP:
                continue
            target = next((m for r, m in replaced.items() if re.search(r'\b' + re.escape(r) + r'\b', line)), None)
            if target:
                # The sibling is an earlier section of this file.
                own.append('Import %s.' % target)
            else:
                own.append(line)
                if line not in requires:
                    requires.append(line)
            continue
        body.append(line)
    body = '\n'.join(body)
    cut = None
    if stop:
        m = re.search(r'^(Lemma|Definition|Theorem) ' + re.escape(stop) + r'\b', body, re.M)
        assert m, (rel, stop)
        body, cut = body[:m.start()], stop
    manifest.append(dict(source=rel, sha256=hashlib.sha256(text.encode()).hexdigest(), module=name,
                         copied_lines=body.strip('\n').count('\n') + 1, cut_before=cut,
                         dropped_imports=[l for l in text.split('\n') if l in DROP]))
    # Each section repeats its own import lines, so every copied body sees the
    # same names and scopes as in its source file.
    imports_local = '\n'.join(l if not l.startswith(('Require', 'From')) else
                              re.sub(r'\bRequire Import\b', 'Import', re.sub(r'^From (\S+) Require Import', r'From \1 Require Import', l))
                              for l in own)
    bodies.append('(* Verbatim copy of %s%s. *)\nModule %s.\n%s\n%s\nEnd %s.\n' % (
        rel, (' up to ' + cut) if cut else '', name, '\n'.join(own), body.strip('\n'), name))

header = ('(* Ported pure meaning lemmas: verbatim copies of October modules (see PORT.json).\n'
          '   It imports neither core umbrella. *)\n' + '\n'.join(l.replace(' Require Import ', ' Require ').replace('Require Import ', 'Require ') for l in requires if not l.startswith('Import ')) + '\n\n')
exports = ''.join('Export %s.\n' % name for _, name, _ in SOURCES)
OUT.write_text(header + '\n'.join(bodies) + '\n' + exports)
(OUT.parent / 'PORT.json').write_text(json.dumps(dict(output=str(OUT), requires=requires, sources=manifest), indent=1))
print(json.dumps([(m['module'], m['copied_lines'], m['cut_before'], m['dropped_imports']) for m in manifest]))
