Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Automation.NatPowerGoals.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec
  WriteSuccessExactTransactionsLayout.

Lemma transactions_live_state_facts `{!islaG Sigma} `{!threadG}
    sp base transactions processed remaining bytes tail (P : iProp Sigma) :
  transactionLiveLoopState sp base transactions processed remaining bytes tail P -∗
  transactionLiveLoopState sp base transactions processed remaining bytes tail P ∗
  ⌜Forall writeSuccessTransactionValid transactions⌝ ∗
  ⌜transactionLoopSourceFacts sp base transactions processed remaining bytes⌝ ∗ True.
Proof.
  iStartProof. iIntros "Hstate".
  iDestruct "Hstate" as
    "(Hsys & Hregs & Hsp & H10 & H11 & Hbytes & Hown & Hscratch & Hmmio & Htrace & %Hfacts & HP & _)".
  iDestruct (exact_transactions_own_valid with "Hown") as "(Hown & %Hvalid & _)".
  iEval (unfold transactionLiveScratch) in "Hscratch".
  zesu_open_resource_groups.
  iSplitL; last done.
  unfold transactionLiveLoopState. zesu_run_nat_safe.
Qed.
Print Assumptions transactions_live_state_facts.
