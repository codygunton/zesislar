Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_38 Require Import instrs.
From IslaTraces.write_success_39 Require Import instrs.
From IslaTraces.write_success_42 Require Import instrs.

Definition transactionPriorityBranchState `{!islaG Sigma} `{!threadG}
    (tag : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x27" ↦ᵣ RVal_Bits tag ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPriorityBranchState) := I.

Lemma transactions_priority_branch_correct `{!islaG Sigma} `{!threadG}
    tag (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_38.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1511c (transactionPriorityBranchState tag P ∗ ⌜tag <> BV 64 0⌝ ∗ True) -∗
  instr_body 0x1513c (transactionPriorityBranchState tag P ∗ ⌜tag = BV 64 0⌝ ∗ True) -∗
  instr_body 0x15118 (transactionPriorityBranchState tag P).
Proof. zesu_block. Qed.
Print Assumptions transactions_priority_branch_correct.

Definition transactionPriorityBooleanJumpEntry `{!islaG Sigma} `{!threadG}
    (old_ra old_data : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPriorityBooleanJumpEntry) := I.

Definition transactionPriorityBooleanJumpPost `{!islaG Sigma} `{!threadG}
    (present : bool) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (if present then BV 64 0x15128 else BV 64 0x15148) ∗
   "x10" ↦ᵣ RVal_Bits (if present then BV 64 1 else BV 64 0) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPriorityBooleanJumpPost) := I.

Lemma transactions_priority_boolean_jump_correct `{!islaG Sigma} `{!threadG}
    (present : bool) old_ra old_data (P : iProp Sigma) :
  ([∗ list] instruction ∈ (if present then IslaTraces.write_success_39.instrs.instr_map
    else IslaTraces.write_success_42.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c (transactionPriorityBooleanJumpPost present P) -∗
  instr_body (if present then 0x1511c else 0x1513c)
    (transactionPriorityBooleanJumpEntry old_ra old_data P).
Proof. destruct present; zesu_block. Qed.
Print Assumptions transactions_priority_boolean_jump_correct.
