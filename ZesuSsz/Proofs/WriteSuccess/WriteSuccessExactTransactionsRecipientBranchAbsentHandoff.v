Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientBranchHandoff WriteSuccessExactTransactionsRecipientBranch
  WriteSuccessExactTransactionsRecipientAbsentRegion WriteSuccessExactTransactionsRecipientAbsentToValue.

Lemma transactions_recipient_branch_to_absent `{!islaG Sigma} `{!threadG}
    (sp tag first second w0 w1 w2 w3 oldra old5 old11 old12 old13 : bv 64)
    (last : bv 32) tail (P : iProp Sigma) :
  (transactionRecipientBranchState sp tag tag
    (transactionRecipientBranchCallerFrame sp tag first second w0 w1 w2 w3
      oldra old5 old11 old12 old13 last tail P) ∗ ⌜tag = BV 64 0⌝ ∗ True)%I -∗
  transactionRecipientAbsentEntry sp first second w0 w1 w2 w3
    oldra old5 old11 old12 old13 last tail
    ((bv_unsigned sp + 120) ↦ₘ tag ∗ P ∗ True).
Proof.
  iIntros "(Hstate & %Htag & _)". subst tag.
  iDestruct "Hstate" as "(Hsys & Hsp & H10 & HtagMemory & %Halign8 & %Hlow8 & %Hhigh8 & Hcaller & _)".
  iDestruct "Hcaller" as "(H1 & H5 & H11 & H12 & H13 & H18 & H20 & Hword2 & H21 & Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & Hscratch & Hmmio & Htrace & %Halign & %Hlow & %Hhigh & HP & _)".
  iEval (rewrite /transactionRecipientValueTrace /=) in "Htrace".
  iDestruct (mem_mapsto_uninit_split 32 with "Hscratch") as "[Hlower Hupper]"; first lia.
  iEval (replace (bv_unsigned sp - 48 + 32)%Z with (bv_unsigned sp - 16)%Z by lia) in "Hupper".
  unfold transactionRecipientAbsentEntry, transactionRecipientAbsentValuePreparation.
  iFrame. repeat iSplit; try done; iPureIntro; first [lia | bv_solve].
Qed.
Print Assumptions transactions_recipient_branch_to_absent.
