Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSpec WriteSuccessExactTransactionsLiveSpec.

Lemma transactions_live_state_complete `{!islaG Sigma} `{!threadG}
    sp base transactions processed remaining bytes tail (P : iProp Sigma) :
  transactionLiveLoopState sp base transactions processed remaining bytes tail P -∗
  ⌜Z_to_bv 64 (Z.of_nat (length processed)) = Z_to_bv 64 (Z.of_nat (length transactions))⌝ -∗
  transactionLiveLoopExit sp base transactions bytes tail P.
Proof.
  iStartProof. iIntros "Hstate %Hcursor".
  iDestruct "Hstate" as "(Hsys & Hregs & Hsp & H10 & H11 & Hbytes & Hown & Hscratch & Hmmio & Htrace & %Hfacts & HP & _)".
  have HfactsCopy := Hfacts. destruct HfactsCopy as (Hrelation & _ & _ & Hbound & _).
  have Hremaining := proj1 (writeSuccessTransactionCursor_complete
    transactions processed remaining Hrelation Hbound) Hcursor.
  subst remaining. rewrite app_nil_r in Hrelation. subst processed.
  iApply transactions_live_state_exit.
  rewrite /transactionLiveLoopState. iFrame. done.
Qed.
Print Assumptions transactions_live_state_complete.
