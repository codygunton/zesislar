Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_43 Require Import instrs.

Definition transactionGasLimitJumpEntry `{!islaG Sigma} `{!threadG}
    (limit old_ra old_data : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x26" ↦ᵣ RVal_Bits limit ∗
   "x1" ↦ᵣ RVal_Bits old_ra ∗ "x10" ↦ᵣ RVal_Bits old_data ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasLimitJumpEntry) := I.

Definition transactionGasLimitJumpPost `{!islaG Sigma} `{!threadG}
    (limit : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x26" ↦ᵣ RVal_Bits limit ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15154) ∗
   "x10" ↦ᵣ RVal_Bits limit ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasLimitJumpPost) := I.

Lemma transactions_gas_limit_jump_correct `{!islaG Sigma} `{!threadG}
    limit old_ra old_data (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_43.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10 (transactionGasLimitJumpPost limit P) -∗
  instr_body 0x15148 (transactionGasLimitJumpEntry limit old_ra old_data P).
Proof. zesu_block. Qed.
Print Assumptions transactions_gas_limit_jump_correct.
