Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_50 Require Import instrs.

Definition transactionDataJumpEntry `{!islaG Sigma} `{!threadG}
    (low high old_ra old_data old_size : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits low ∗
   "x22" ↦ᵣ RVal_Bits high ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ "x11" ↦ᵣ RVal_Bits old_size ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionDataJumpEntry) := I.

Definition transactionDataJumpPost `{!islaG Sigma} `{!threadG}
    (low high : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits low ∗
   "x22" ↦ᵣ RVal_Bits high ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x151c4) ∗
   "x10" ↦ᵣ RVal_Bits low ∗ "x11" ↦ᵣ RVal_Bits high ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionDataJumpPost) := I.

Lemma transactions_data_jump_correct `{!islaG Sigma} `{!threadG}
    low high old_ra old_data old_size (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_50.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c6c (transactionDataJumpPost low high P) -∗
  instr_body 0x151b4 (transactionDataJumpEntry low high old_ra old_data old_size P).
Proof. zesu_block. Qed.
Print Assumptions transactions_data_jump_correct.
