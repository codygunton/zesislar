Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_65 Require Import instrs.

Lemma blob_initial_empty `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_65.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15564 (reg_col zesu_ram_sys_regs ∗ "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗ P ∗ True)%I -∗
  instr_body 0x153d0 (reg_col zesu_ram_sys_regs ∗ "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗ P ∗ True)%I.
Proof. zesu_block. Qed.
Print Assumptions blob_initial_empty.
