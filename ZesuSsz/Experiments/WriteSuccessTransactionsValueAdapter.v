From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSemanticAdapter.

Definition writeSuccessTransactionsValueAdapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∀ (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
      (tail : spec),
    ⌜default (BV 64 0) (values !! 8%nat) ≠ BV 64 0⌝ -∗
    writeSuccessValuePost sp values payload tail P -∗
    writeSuccessTransactionsLoopSpec P)%I.

Definition writeSuccessOuterNonemptyValueSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
      (tail : spec),
    writeSuccessValuePost sp values payload tail P ∗
    ⌜default (BV 64 0) (values !! 8%nat) ≠ BV 64 0⌝ ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessOuterNonemptyValueSpec) := I.

Lemma write_success_outer_nonempty_transactions_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ writeSuccessTransactionsValueAdapter P -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) -∗
  □ instr_pre 0x14f04 (writeSuccessOuterNonemptyValueSpec P).
Proof.
  iStartProof.
  iIntros "#Hadapter #Hloop".
  iApply (write_success_transactions_semantic_adapter_pre
    (writeSuccessOuterNonemptyValueSpec P) P with "[] Hloop").
  iModIntro.
  iEval (rewrite /writeSuccessTransactionsSemanticAdapter).
  iIntros "Hentry".
  iEval (rewrite /writeSuccessOuterNonemptyValueSpec) in "Hentry".
  iDestruct "Hentry" as (sp values payload tail) "(Hpost & %Hnonempty & _)".
  iEval (rewrite /writeSuccessTransactionsValueAdapter) in "Hadapter".
  iApply ("Hadapter" $! sp values payload tail with "[] Hpost").
  iPureIntro. exact Hnonempty.
Qed.
