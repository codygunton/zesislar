#!/usr/bin/env python3
"""Assemble the shared ported meaning module by verbatim copy.

Each source file's body (everything after its import lines) is copied byte for
byte into its own `Module` section. A section repeats its source's own import
lines, so the copied text sees the same names and scopes as in its source.
Changes are limited to import lines:
- the frozen umbrella `ZesuSsz.Automation.All` becomes `Import ZesuSsz.Automation2.Hooks.`
  (the owner of `lia` and `bv_solve`);
- a frozen leaf module with an identical Automation2 copy becomes that copy;
- an import of a module that an earlier section replaces becomes `Import <section>.`;
- listed unused imports are dropped.
A source can be cut (`start`/`stop` at a top-level command) or reduced to named
top-level items (`items`). Nothing inside a copied command is rewritten.
Usage: port_meaning_lemmas.py WORKTREE OUTPUT.v"""
import hashlib, json, os, re, sys
from pathlib import Path

W = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2])
C = 'ZesuSsz/Compliance/'
SOURCES = [
    dict(src='ZesuSsz/Contracts/RlpDecodeItemReturnImages.v', name='PortedReturnImages'),
    dict(src=C + 'DecodeItemSemanticIntroduction.v', name='PortedSemanticIntroduction'),
    dict(src=C + 'DecodeItemSailEvaluation.v', name='PortedSailEvaluation'),
    dict(src=C + 'DecodeItemSailIntroduction.v', name='PortedSailIntroduction',
         stop='decodeItemLongCandidateFromProvenance',
         drop=['Require Import ZesuSsz.Compliance.DecodeItemSailFold.',
               'Require Import ZesuSsz.Compliance.ByteFold.']),
    dict(src=C + 'DecodeItemPathAgreement.v', name='PortedPathAgreement'),
    dict(src=C + 'DecodeItemReturnExitResources.v', name='PortedReturnExitResources'),
    dict(src=C + 'DecodeItemReturnExitPure.v', name='PortedReturnExitPure'),
    # Long-class Sail facts (6a40, 6b08).
    dict(src=C + 'ByteFold.v', name='PortedByteFold'),
    dict(src=C + 'DecodeItemSailFold.v', name='PortedSailFold',
         drop=['Require Import ZesuSsz.Proofs.DecodeItem.ByteFoldPure.']),
    dict(src=C + 'DecodeItemSailIntroduction.v', name='PortedSailIntroductionLong',
         start='decodeItemLongCandidateFromProvenance', after='PortedSailIntroduction'),
    # Output-image and byte lemmas (6a78, 6a40, 6b08).
    dict(src='ZesuSsz/Contracts/DecodeItemFrameImage.v', name='PortedFrameImage',
         items=['littleEndian_machine_bytes'],
         drop=['Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.',
               'Require Import ZesuSsz.Automation.ByteArrays.']),
    dict(src=C + 'DecodeItemReturnRestorationFacts.v', name='PortedRestoration',
         items=['decodeItemByteDecoderBridge'],
         drop=['Require Import ZesuSsz.Automation.Approved.',
               'Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.']),
    dict(src=C + 'DecodeItemRawOutputFacts.v', name='PortedRawOutput',
         items=['decodeItemRawOutputStatus', 'decodeItemRawOutputPad17', 'decodeItemRawOutputPad34',
                'decodeItemRawOutputExtent', 'decodeItemRawInputPointer', 'decodeItemRawInputSuccessor']),
    dict(src=C + 'DecodeItemOutputBaseWitnessFacts.v', name='PortedOutputBase',
         items=['decodeItemOutputBaseOffset', 'decodeItemFlagUpdatedBaseBound', 'decodeItemOutputOffset8',
                'decodeItemOutputOffset16', 'decodeItemOutputStorageExtent16',
                'decodeItemOutputStorageExtent24', 'decodeItemOutputWord32Length'],
         drop=['Require Import ZesuSsz.Automation.Switches.PureFactHints.']),
    dict(src=C + 'DecodeItemJoinMeaning.v', name='PortedJoinMeaning'),
    # October fold vocabulary (long headers); the new loop-exit entries state the
    # fold with zesu_byte_window_fold, so these need a bridge lemma to apply.
    dict(src='ZesuSsz/Contracts/RlpDecodeItemByteFold.v', name='PortedByteFoldContract',
         items=['decodeItemByteFoldFacts', 'decodeItemByteFoldFirstGuard'],
         drop=['Require Import ZesuSsz.Contracts.IslarisCode.']),
    dict(src='ZesuSsz/Contracts/RlpDecodeItemByteFoldBlocks.v', name='PortedFoldBlocks',
         items=['decodeItemFoldLengthFits'],
         drop=['Require Import isla.riscv64.riscv64.', 'Require Import InstrSpecs.Machine.',
               'Require Import ZesuSsz.Contracts.DecodeItemSelected.',
               'Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.']),
    dict(src=C + 'DecodeItemFoldRejectionFacts.v', name='PortedFoldRejection',
         items=['decodeItemCompletedFoldRejected'], after='PortedSailIntroductionLong'),
    dict(src=C + 'DecodeItemHeaderWitnessFacts.v', name='PortedHeaderWitness',
         items=['decodeItemInputHeadWitnessFacts', 'decodeItemStringHeaderProvenanceFacts',
                'decodeItemListHeaderProvenanceFacts', 'decodeItemHeaderInitialFoldFacts',
                'decodeItemStringHeaderReadGuardFacts', 'decodeItemListHeaderReadGuardFacts',
                'decodeItemHeaderUnsignedReadGuardFacts', 'decodeItemCompletedFoldAcceptedWitnessFacts',
                'decodeItemCompletedFoldConsumedWord', 'decodeItemCompletedFoldFitsGuard',
                'decodeItemCompletedFoldRejectGuard', 'decodeItemInputPointerCastWitnessFacts',
                'decodeItemCompletedFoldFitsContradiction', 'decodeItemCompletedFoldAlternateFitsContradiction'],
         after='PortedSailIntroductionLong',
         drop=['Require Import ZesuSsz.Automation.Switches.PureFactHints.',
               'Require Import ZesuSsz.Compliance.DecodeItemDataWitnessFacts.',
               'Require Export ZesuSsz.Compliance.DecodeItemEntryGuardFacts.',
               'Require Import ZesuSsz.Compliance.DecodeItemInputHeadWordFacts.']),
]
if os.environ.get('PORT_SECTIONS'):
    SOURCES = SOURCES[:int(os.environ['PORT_SECTIONS'])]
FROZEN_ALL = 'Require Import ZesuSsz.Automation.All.'
FROZEN_SUBSTITUTE = os.environ.get('PORT_FROZEN_SUBSTITUTE', 'Import ZesuSsz.Automation2.Hooks.')
# Frozen modules with an identical (or same-named) Automation2 copy.
LEAF_COPIES = {f'{k} ZesuSsz.Automation.{m}.': f'{k} ZesuSsz.Automation2.{m}.'
               for m in ('SailEval', 'PureFacts', 'ByteFold', 'AdditiveDecoder', 'JoinEntailment',
                         'BitvectorFacts', 'MemoryAddress')
               for k in ('Require Import', 'Require Export')}
IMPORT = re.compile(r'^(Require|From \S+ Require)\b')
COMMAND = re.compile(r'^(?:#\[[^\]]*\]\s*)?(?:Local |Global )?(Lemma|Theorem|Definition|Fixpoint|Ltac|Instance|'
                     r'Hint|Print|Notation|Arguments|Opaque|Transparent|Existing|Remove|Typeclasses)\b\s*(\S*)')
replaced = {}


def chunks(body):
    """Split a body into top-level commands; each starts at a column-0 command keyword."""
    out, current = [], None
    for line in body.split('\n'):
        m = COMMAND.match(line)
        if m:
            current = dict(kind=m.group(1), name=m.group(2).rstrip(':'), lines=[line])
            out.append(current)
        elif current is None or (not line.strip() == '' and not line.startswith((' ', '\t', ')', '|', '-', '+', '*', '}', '{')) and current['kind'] not in ('Lemma', 'Theorem', 'Definition', 'Fixpoint', 'Ltac', 'Instance', 'Hint', 'Notation')):
            current = dict(kind='env', name='', lines=[line])
            out.append(current)
        else:
            current['lines'].append(line)
    return out


requires, bodies, manifest = [], [], []
for spec in SOURCES:
    rel, name = spec['src'], spec['name']
    text = (W / rel).read_text()
    own, body = [], []
    for line in text.split('\n'):
        if IMPORT.match(line):
            if line == FROZEN_ALL and FROZEN_SUBSTITUTE:
                own.append(FROZEN_SUBSTITUTE)
                owner = 'Require ' + FROZEN_SUBSTITUTE.split()[1]
                if owner not in requires:
                    requires.append(owner)
                continue
            if line in spec.get('drop', []):
                continue
            line = LEAF_COPIES.get(line, line)
            target = next((m for r, m in replaced.items() if re.search(r'\b' + re.escape(r) + r'\b', line)), None)
            if target:
                own.append('Import %s.' % target)
            else:
                own.append(line)
                if line not in requires:
                    requires.append(line)
            continue
        body.append(line)
    if spec.get('after'):
        own.append('Import %s.' % spec['after'])
    body = '\n'.join(body)
    if spec.get('start'):
        m = re.search(r'^(Lemma|Definition|Theorem) ' + re.escape(spec['start']) + r'\b', body, re.M)
        assert m, (rel, spec['start'])
        # Keep the scope and notation lines before the cut point.
        prefix = '\n'.join(l for l in body[:m.start()].split('\n')
                           if l.startswith(('Import ', 'Open Scope', 'Local Open Scope')))
        body = prefix + '\n\n' + body[m.start():]
    if spec.get('stop'):
        m = re.search(r'^(Lemma|Definition|Theorem) ' + re.escape(spec['stop']) + r'\b', body, re.M)
        assert m, (rel, spec['stop'])
        body = body[:m.start()]
    if spec.get('items'):
        kept = []
        for c in chunks(body):
            if c['kind'] == 'env':
                kept += [l for l in c['lines'] if l.startswith(('Import ', 'Open Scope', 'Local Open Scope'))]
            elif c['name'] in spec['items']:
                kept += c['lines']
        missing = [i for i in spec['items'] if not re.search(r'\b' + re.escape(i) + r'\b', '\n'.join(kept))]
        assert not missing, (rel, missing)
        body = '\n'.join(kept)
    manifest.append(dict(source=rel, sha256=hashlib.sha256(text.encode()).hexdigest(), module=name,
                         copied_lines=body.strip('\n').count('\n') + 1, start=spec.get('start'),
                         stop=spec.get('stop'), items=spec.get('items')))
    bodies.append('(* Verbatim copy of %s%s. *)\nModule %s.\n%s\n%s\nEnd %s.\n' % (
        rel, (' from ' + spec['start']) if spec.get('start') else (' up to ' + spec['stop']) if spec.get('stop')
        else (' (items: ' + ', '.join(spec['items']) + ')') if spec.get('items') else '',
        name, '\n'.join(own), body.strip('\n'), name))
    replaced.setdefault('ZesuSsz.' + rel[len('ZesuSsz/'):-2].replace('/', '.'), name)

header = ('(* Ported pure meaning lemmas: verbatim copies of October modules (see the copy notes).\n'
          '   It imports neither core umbrella. Generated by tools/block/port_meaning_lemmas.py. *)\n'
          + '\n'.join(l.replace(' Require Import ', ' Require ').replace('Require Import ', 'Require ')
                      .replace('Require Export ', 'Require ') for l in requires if not l.startswith('Import '))
          + '\n\n')
exports = ''.join('Export %s.\n' % s['name'] for s in SOURCES)
OUT.write_text(header + '\n'.join(bodies) + '\n' + exports)
print(json.dumps([(m['module'], m['copied_lines']) for m in manifest]))
