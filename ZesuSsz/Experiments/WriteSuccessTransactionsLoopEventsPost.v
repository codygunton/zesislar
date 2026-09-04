From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15668Events.

Definition writeSuccessTransactionsLoopEventsPostSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec) (first second : bv 64)
      (items : list ByteListItem),
    writeSuccessTransactionsLoopEventsFrame P sp base transactions processed
      remaining bytes prefix suffix tail first second items
      (writeSuccessTransactionsPostAt15668EventsSpec P))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopEventsPostSpec) := I.

Lemma write_success_transactions_loop_events_exit_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsLoopEventsPostSpec P -∗
  writeSuccessTransactionsLoopEventsSpec P.
Proof.
  iStartProof. iIntros "Hloop".
  iEval (unfold writeSuccessTransactionsLoopEventsPostSpec) in "Hloop".
  iDestruct "Hloop" as
    (sp base transactions processed remaining bytes prefix suffix tail first second items)
    "Hframe".
  iExists sp, base, transactions, processed, remaining, bytes, prefix, suffix,
    tail, first, second, items.
  iEval (unfold writeSuccessTransactionsLoopEventsFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hsys & Hother & H2 & H10 & H11 & Hprefix & Hsuffix & Hprocessed & Hremaining &
      Hscratch & Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  iAssert (instr_pre 0x15668
    (writeSuccessTransactionsLoopExitEvents P sp base transactions bytes tail
      first second items))%I
    with "[Hexit]" as "Hpost".
  { iApply (instr_pre_wand 0x15668 0x15668 true true with "Hexit");
      [done | reflexivity |].
    iIntros "HloopExit".
    iApply write_success_transactions_loop_exit_events_handoff.
    iExact "HloopExit". }
  iEval (unfold writeSuccessTransactionsLoopEventsFrame).
  iFrame "Hsys Hother H2 H10 H11 Hprefix Hsuffix Hprocessed Hremaining Hscratch
    Hmmio Htrace HP Hinvariant Hpost".
Qed.

Lemma write_success_transactions_loop_events_parent
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopEventsSpec P) -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopEventsPostSpec P).
Proof.
  iStartProof. iIntros "#Hloop".
  iModIntro.
  iApply (instr_pre_wand 0x14f04 0x14f04 true true with "Hloop");
    [done | reflexivity |].
  iIntros "Hentry".
  iApply (write_success_transactions_loop_events_exit_adapter P with "Hentry").
Qed.
