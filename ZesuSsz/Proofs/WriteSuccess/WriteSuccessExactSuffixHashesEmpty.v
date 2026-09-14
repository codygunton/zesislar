Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_102 Require Import instrs.

Lemma suffix_initial_empty `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_102.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x158e0 (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ P ∗ True)%I -∗
  instr_body 0x15750 (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ P ∗ True)%I.
Proof. zesu_block. Qed.
Print Assumptions suffix_initial_empty.
