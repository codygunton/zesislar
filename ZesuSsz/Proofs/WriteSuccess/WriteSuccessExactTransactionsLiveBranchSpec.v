Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsSpec
  WriteSuccessExactTransactionsLiveSpec WriteSuccessExactTransactionsBranch.

Definition transactionLiveBranchFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed remaining : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessTransactionsOtherRegShapes ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   transactionLiveScratch sp base (length transactions) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactTransactionsEvents sp remaining tail) ∗
   ⌜transactionLoopSourceFacts sp base transactions processed remaining bytes⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionLiveBranchFrame) := I.

Lemma transactions_live_state_branch `{!islaG Sigma} `{!threadG}
    sp base transactions processed remaining bytes tail (P : iProp Sigma) :
  transactionLiveLoopState sp base transactions processed remaining bytes tail P ⊣⊢
  exactTransactionsBranchState (Z_to_bv 64 (Z.of_nat (length transactions)))
    (Z_to_bv 64 (Z.of_nat (length processed)))
    (transactionLiveBranchFrame sp base transactions processed remaining bytes tail P).
Proof.
  rewrite /transactionLiveLoopState /exactTransactionsBranchState /transactionLiveBranchFrame.
  apply zesu_branch_resource_equiv.
Qed.
Print Assumptions transactions_live_state_branch.
