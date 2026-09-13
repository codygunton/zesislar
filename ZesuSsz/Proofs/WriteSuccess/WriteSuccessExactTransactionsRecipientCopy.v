Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From Coq Require Import Lists.List.
From IslaTraces.write_success_45 Require Import instrs.

Definition transactionRecipientCopyEntry `{!islaG Sigma} `{!threadG}
    (sp first second : bv 64) (last : bv 32) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64)] ∗
   (bv_unsigned sp + 1640) ↦ₘ first ∗
   (bv_unsigned sp + 1648) ↦ₘ second ∗ (bv_unsigned sp + 1656) ↦ₘ last ∗
   (bv_unsigned sp + 1744) ↦ₘ? 20 ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1764 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientCopyEntry) := I.

Definition transactionRecipientCopyPost `{!islaG Sigma} `{!threadG}
    (sp first second : bv 64) (last : bv 32) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits first ∗ "x11" ↦ᵣ RVal_Bits second ∗
   "x12" ↦ᵣ RVal_Bits (bv_sign_extend 64 last) ∗
   (bv_unsigned sp + 1640) ↦ₘ first ∗
   (bv_unsigned sp + 1648) ↦ₘ second ∗ (bv_unsigned sp + 1656) ↦ₘ last ∗
   (bv_unsigned sp + 1744) ↦ₘ first ∗
   (bv_unsigned sp + 1752) ↦ₘ second ∗ (bv_unsigned sp + 1760) ↦ₘ last ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1764 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientCopyPost) := I.

Lemma transactions_recipient_copy_correct `{!islaG Sigma} `{!threadG}
    sp first second last (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_45.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15174 (transactionRecipientCopyPost sp first second last P) -∗
  instr_body 0x1515c (transactionRecipientCopyEntry sp first second last P).
Proof. zesu_block. Qed.
Print Assumptions transactions_recipient_copy_correct.
