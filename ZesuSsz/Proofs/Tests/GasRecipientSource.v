Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasRecipientSource WriteSuccessExactTransactionsGasToRecipient.

Lemma gas_recipient_source_factor_preserves_resources `{!islaG Sigma} `{!threadG}
    (sp tag first second w0 w1 w2 w3 old12 old13 data size count old6 : bv 64)
    (last : bv 32) (bytes : list (bv 8)) (P : iProp Sigma) :
  transactionGasRecipientSourceCaller sp tag first second w0 w1 w2 w3 old12 old13
    data size count old6 last bytes P ⊣⊢
  ("x12" ↦ᵣ RVal_Bits old12 ∗ "x13" ↦ᵣ RVal_Bits old13 ∗
   "x18" ↦ᵣ RVal_Bits w0 ∗ "x20" ↦ᵣ RVal_Bits w1 ∗
   (bv_unsigned sp + 128) ↦ₘ w2 ∗ "x21" ↦ᵣ RVal_Bits w3 ∗
   (bv_unsigned sp + 120) ↦ₘ tag ∗
   (bv_unsigned sp + 1640) ↦ₘ first ∗ (bv_unsigned sp + 1648) ↦ₘ second ∗
   (bv_unsigned sp + 1656) ↦ₘ last ∗ (bv_unsigned sp + 1744) ↦ₘ? 20 ∗
   (bv_unsigned sp - 48) ↦ₘ? 16 ∗
   "x8" ↦ᵣ RVal_Bits data ∗ "x22" ↦ᵣ RVal_Bits size ∗ "x6" ↦ᵣ RVal_Bits old6 ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ ⌜bv_unsigned size = length bytes⌝ ∗
   (bv_unsigned sp + 264) ↦ₘ count ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1764 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Proof.
  unfold transactionGasRecipientSourceCaller, transactionGasRecipientSourceCore. iSplit.
  - iIntros "(H8 & H6 & Hcore & _)".
    iDestruct "Hcore" as "(H12 & H13 & H18 & H20 & Hword2 & H21 & Htag & Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & Hlower & H22 & HdataBytes & Hlen & Hcount & Halign & Hlow & Hhigh & HP & _)".
    iFrame.
  - iIntros "(H12 & H13 & H18 & H20 & Hword2 & H21 & Htag & Hsrc0 & Hsrc1 & Hsrc2 & Hdestination & Hlower & H8 & H22 & H6 & HdataBytes & Hlen & Hcount & Halign & Hlow & Hhigh & HP & _)".
    iFrame.
Qed.
Print Assumptions gas_recipient_source_factor_preserves_resources.
