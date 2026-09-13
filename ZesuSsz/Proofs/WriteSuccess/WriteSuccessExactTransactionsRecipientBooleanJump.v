Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_45 Require Import instrs.
From IslaTraces.write_success_48 Require Import instrs.

Definition transactionRecipientBooleanJumpEntry `{!islaG Sigma} `{!threadG}
    (present : bool) (old_ra old_data : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x10" ↦ᵣ RVal_Bits (if present then old_data else BV 64 0) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientBooleanJumpEntry) := I.

Definition transactionRecipientBooleanJumpPost `{!islaG Sigma} `{!threadG}
    (present : bool) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (if present then BV 64 0x15180 else BV 64 0x1519c) ∗
   "x10" ↦ᵣ RVal_Bits (if present then BV 64 1 else BV 64 0) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientBooleanJumpPost) := I.

Lemma transactions_recipient_boolean_jump_correct `{!islaG Sigma} `{!threadG}
    (present : bool) old_ra old_data (P : iProp Sigma) :
  ([∗ list] instruction ∈ (if present then take 3 (drop 6
    IslaTraces.write_success_45.instrs.instr_map)
    else IslaTraces.write_success_48.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c (transactionRecipientBooleanJumpPost present P) -∗
  instr_body (if present then 0x15174 else 0x15194)
    (transactionRecipientBooleanJumpEntry present old_ra old_data P).
Proof. destruct present; zesu_block. Qed.
Print Assumptions transactions_recipient_boolean_jump_correct.
