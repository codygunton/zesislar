Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CallScratchSized.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactTransactionsPriority
  WriteSuccessExactEncoderU128.

Definition transactionGasPricePriorityFrame `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15118) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   transactionGasPriceFrame sp low high P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasPricePriorityFrame) := I.

Lemma transactions_gas_price_to_priority `{!islaG Sigma} `{!threadG}
    (sp low high tag : bv 64) tail (P : iProp Sigma) :
  transactionGasPricePost sp low high tail ("x27" ↦ᵣ RVal_Bits tag ∗ P ∗ True)%I -∗
  transactionPriorityBranchState tag (transactionGasPricePriorityFrame sp low high tail P).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hpayload & Hgap & Hret & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hhighword & Hlowword & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Htag & HP & _)".
  have Hlen : length (writeSuccessU128WordsPayload low high) = N.to_nat 16 by reflexivity.
  have Hoffset : Z_to_bv 64 (Z.of_N 16 + 16) = BV 64 32 by bv_solve.
  iEval (rewrite -Hoffset) in "Hpayload".
  iPoseProof (call_scratch_reuse_sized sp (BV 64 0x15118) _ 16 Hlen Hlow
    with "[$Hpayload $Hgap $Hret]") as "Hscratch".
  unfold transactionPriorityBranchState, transactionGasPricePriorityFrame, transactionGasPriceFrame.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_gas_price_to_priority.
