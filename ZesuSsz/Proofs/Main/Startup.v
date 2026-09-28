Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import IslaTraces.startup.instrs.

Lemma main_startup_block `{!islaG Sigma} `{!threadG}
    (oldRa oldGp : bv 64) (P : iProp Sigma) :
  ([∗ list] i ∈ IslaTraces.startup.instrs.instr_map, instr i.1 (Some i.2)) -∗
  instr_body 0x14cb0
    (reg_col zesu_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x1012c) ∗
     "x3" ↦ᵣ RVal_Bits (BV 64 0x19800) ∗ P ∗ True) -∗
  instr_body 0x10120
    (reg_col zesu_sys_regs ∗ "x1" ↦ᵣ RVal_Bits oldRa ∗
     "x3" ↦ᵣ RVal_Bits oldGp ∗ P ∗ True).
Proof.
  zesu_block.
Qed.
Print Assumptions main_startup_block.
