Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsBranch.

Import ListNotations.

Definition writeSuccessExactTransactionsBranchFrame
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsScratch sp base (length transactions) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactTransactionsEvents sp remaining tail) ∗
   ⌜transactions = processed ++ remaining⌝ ∗
   ⌜bytes = writeSuccessTransactionsBytes transactions⌝ ∗
   ⌜length bytes = (288 * length transactions)%nat⌝ ∗
   ⌜(length transactions < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   ⌜base `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessExactTransactionsBranchFrame) := I.

Lemma writeSuccessExactTransactionsState_branch
    `{!islaG Sigma} `{!threadG} sp base transactions processed remaining bytes
    tail (P : iProp Sigma) :
  writeSuccessExactTransactionsState sp base transactions processed remaining
    bytes tail P ⊣⊢
  exactTransactionsBranchState
    (Z_to_bv 64 (Z.of_nat (length transactions)))
    (Z_to_bv 64 (Z.of_nat (length processed)))
    (writeSuccessExactTransactionsBranchFrame sp base transactions processed
      remaining bytes tail P).
Proof.
  rewrite /writeSuccessExactTransactionsState /exactTransactionsBranchState
    /writeSuccessExactTransactionsBranchFrame.
  apply zesu_branch_resource_equiv.
Qed.
Print Assumptions writeSuccessExactTransactionsState_branch.

Lemma writeSuccessExactTransactionsState_facts
    `{!islaG Sigma} `{!threadG} sp base transactions processed remaining bytes
    tail (P : iProp Sigma) :
  writeSuccessExactTransactionsState sp base transactions processed remaining
    bytes tail P -∗
  ⌜transactions = processed ++ remaining⌝ ∗
  ⌜(length transactions < 2 ^ 64)%nat⌝ ∗
  writeSuccessExactTransactionsState sp base transactions processed remaining
    bytes tail P ∗ True.
Proof.
  rewrite /writeSuccessExactTransactionsState.
  iIntros "(Hsys & Hregs & H2 & H10 & H11 & Hmem & Hown & Hscratch &
    Hmmio & Htrace & %Hrelation & %Hbytes & %Hlength & %Hbound & Hrest)".
  iSplit; first (iPureIntro; exact Hrelation).
  iSplit; first (iPureIntro; exact Hbound).
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions writeSuccessExactTransactionsState_facts.
Lemma writeSuccessExactTransactionsState_complete
    `{!islaG Sigma} `{!threadG} sp base transactions processed remaining bytes
    tail (P : iProp Sigma) :
  writeSuccessExactTransactionsState sp base transactions processed remaining
    bytes tail P -∗
  ⌜Z_to_bv 64 (Z.of_nat (length processed)) =
    Z_to_bv 64 (Z.of_nat (length transactions))⌝ -∗
  writeSuccessTransactionsLoopExit sp base transactions bytes tail P.
Proof.
  rewrite /writeSuccessExactTransactionsState.
  iIntros "(Hsys & Hregs & H2 & H10 & H11 & Hmem & Hown & Hscratch &
    Hmmio & Htrace & %Hrelation & %Hbytes & %Hlength & %Hbound & Hrest) %Hcursor".
  have Hremaining := proj1 (writeSuccessTransactionCursor_complete
    transactions processed remaining Hrelation Hbound) Hcursor.
  subst remaining. rewrite app_nil_r in Hrelation. subst transactions.
  iEval (rewrite /writeSuccessExactTransactionsEvents
    /writeSuccessExactTransactionsPayloads /=) in "Htrace".
  iDestruct "Hrest" as "(_ & _ & _ & _ & _ & _ & HP & _)".
  rewrite /writeSuccessTransactionsLoopExit. iFrame.
Qed.
Print Assumptions writeSuccessExactTransactionsState_complete.

Lemma writeSuccessExactTransactionsState_nonempty
    `{!islaG Sigma} `{!threadG} sp base transactions processed remaining bytes
    tail (P : iProp Sigma) :
  writeSuccessExactTransactionsState sp base transactions processed remaining
    bytes tail P -∗
  ⌜Z_to_bv 64 (Z.of_nat (length processed)) <>
    Z_to_bv 64 (Z.of_nat (length transactions))⌝ -∗
  writeSuccessExactTransactionsState sp base transactions processed remaining
    bytes tail P ∗ ⌜remaining <> []⌝ ∗ True.
Proof.
  rewrite /writeSuccessExactTransactionsState.
  iIntros "(Hsys & Hregs & H2 & H10 & H11 & Hmem & Hown & Hscratch &
    Hmmio & Htrace & %Hrelation & %Hbytes & %Hlength & %Hbound & Hrest) %Hcursor".
  have Hremaining : remaining <> [].
  { intros ->. rewrite app_nil_r in Hrelation. subst transactions.
    apply Hcursor. reflexivity. }
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions writeSuccessExactTransactionsState_nonempty.
