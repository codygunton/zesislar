Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Definition transactionGasRecipientSourceCore `{!islaG Sigma} `{!threadG}
    (sp tag first second w0 w1 w2 w3 old12 old13 data size count : bv 64)
    (last : bv 32) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x12" ↦ᵣ RVal_Bits old12 ∗ "x13" ↦ᵣ RVal_Bits old13 ∗
   "x18" ↦ᵣ RVal_Bits w0 ∗ "x20" ↦ᵣ RVal_Bits w1 ∗
   (bv_unsigned sp + 128) ↦ₘ w2 ∗ "x21" ↦ᵣ RVal_Bits w3 ∗
   (bv_unsigned sp + 120) ↦ₘ tag ∗
   (bv_unsigned sp + 1640) ↦ₘ first ∗ (bv_unsigned sp + 1648) ↦ₘ second ∗
   (bv_unsigned sp + 1656) ↦ₘ last ∗ (bv_unsigned sp + 1744) ↦ₘ? 20 ∗
   (bv_unsigned sp - 48) ↦ₘ? 16 ∗ "x22" ↦ᵣ RVal_Bits size ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ ⌜bv_unsigned size = length bytes⌝ ∗
   (bv_unsigned sp + 264) ↦ₘ count ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1764 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasRecipientSourceCore) := I.
