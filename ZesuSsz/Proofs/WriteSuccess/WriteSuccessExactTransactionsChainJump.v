Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_35 Require Import instrs.

Definition transactionChainJumpEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old_data : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits old_ra ∗ "x10" ↦ᵣ RVal_Bits old_data ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionChainJumpEntry) := I.

Definition transactionChainJumpPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x150fc) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1664)%bv ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionChainJumpPost) := I.

Lemma transactions_chain_jump_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old_data (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_35.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 (transactionChainJumpPost sp P) -∗
  instr_body 0x150f0 (transactionChainJumpEntry sp old_ra old_data P).
Proof. zesu_block. Qed.
Print Assumptions transactions_chain_jump_correct.
