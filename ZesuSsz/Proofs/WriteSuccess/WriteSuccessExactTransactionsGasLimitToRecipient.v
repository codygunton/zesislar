Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasLimitCall WriteSuccessExactTransactionsRecipientBranch.

Definition transactionGasLimitRecipientFrame `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits (BV 64 0x15154) ∗ "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ transactionGasLimitFrame sp value P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasLimitRecipientFrame) := I.

Lemma transactions_gas_limit_to_recipient `{!islaG Sigma} `{!threadG}
    (sp value tag : bv 64) tail (P : iProp Sigma) :
  transactionGasLimitPost sp value tail
    ((bv_unsigned sp + 120) ↦ₘ tag ∗ ⌜bv_unsigned sp + 128 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I -∗
  transactionRecipientBranchState sp tag (sp - BV 64 16)%bv
    (transactionGasLimitRecipientFrame sp value tail P).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hvalue & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Htag & %Hupper & HP & _)".
  unfold transactionRecipientBranchState, transactionGasLimitRecipientFrame, transactionGasLimitFrame.
  iFrame. repeat iSplit; try done; iPureIntro; first [lia | bv_solve].
Qed.
Print Assumptions transactions_gas_limit_to_recipient.
