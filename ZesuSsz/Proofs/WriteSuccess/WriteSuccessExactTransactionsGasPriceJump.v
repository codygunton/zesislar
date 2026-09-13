Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_37 Require Import instrs.

Definition transactionGasPriceJumpEntry `{!islaG Sigma} `{!threadG}
    (low high old_ra old_data old_size : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x25" ↦ᵣ RVal_Bits low ∗
   "x24" ↦ᵣ RVal_Bits high ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ "x11" ↦ᵣ RVal_Bits old_size ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasPriceJumpEntry) := I.

Definition transactionGasPriceJumpPost `{!islaG Sigma} `{!threadG}
    (low high : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x25" ↦ᵣ RVal_Bits low ∗
   "x24" ↦ᵣ RVal_Bits high ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15118) ∗
   "x10" ↦ᵣ RVal_Bits low ∗ "x11" ↦ᵣ RVal_Bits high ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasPriceJumpPost) := I.

Lemma transactions_gas_price_jump_correct `{!islaG Sigma} `{!threadG}
    low high old_ra old_data old_size (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_37.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15ce4 (transactionGasPriceJumpPost low high P) -∗
  instr_body 0x15108 (transactionGasPriceJumpEntry low high old_ra old_data old_size P).
Proof. zesu_block. Qed.
Print Assumptions transactions_gas_price_jump_correct.
