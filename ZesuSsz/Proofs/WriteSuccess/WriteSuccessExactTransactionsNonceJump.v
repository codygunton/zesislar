Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_36 Require Import instrs.

Definition transactionNonceJumpEntry `{!islaG Sigma} `{!threadG}
    (sp nonce old_ra old_data : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits old_ra ∗ "x10" ↦ᵣ RVal_Bits old_data ∗
   (bv_unsigned sp + 272) ↦ₘ nonce ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 280 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNonceJumpEntry) := I.

Definition transactionNonceJumpPost `{!islaG Sigma} `{!threadG}
    (sp nonce : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15108) ∗ "x10" ↦ᵣ RVal_Bits nonce ∗
   (bv_unsigned sp + 272) ↦ₘ nonce ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 280 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNonceJumpPost) := I.

Lemma transactions_nonce_jump_correct `{!islaG Sigma} `{!threadG}
    sp nonce old_ra old_data (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_36.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10 (transactionNonceJumpPost sp nonce P) -∗
  instr_body 0x150fc (transactionNonceJumpEntry sp nonce old_ra old_data P).
Proof. zesu_block. Qed.
Print Assumptions transactions_nonce_jump_correct.
