Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_40 Require Import instrs.

Definition transactionPriorityValueJumpEntry `{!islaG Sigma} `{!threadG}
    (low high old_ra old_data old_size : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits low ∗
   "x23" ↦ᵣ RVal_Bits high ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ "x11" ↦ᵣ RVal_Bits old_size ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPriorityValueJumpEntry) := I.

Definition transactionPriorityValueJumpPost `{!islaG Sigma} `{!threadG}
    (low high : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits low ∗
   "x23" ↦ᵣ RVal_Bits high ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15138) ∗
   "x10" ↦ᵣ RVal_Bits low ∗ "x11" ↦ᵣ RVal_Bits high ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPriorityValueJumpPost) := I.

Lemma transactions_priority_value_jump_correct `{!islaG Sigma} `{!threadG}
    low high old_ra old_data old_size (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_40.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15ce4 (transactionPriorityValueJumpPost low high P) -∗
  instr_body 0x15128 (transactionPriorityValueJumpEntry low high old_ra old_data old_size P).
Proof. zesu_block. Qed.
Print Assumptions transactions_priority_value_jump_correct.
