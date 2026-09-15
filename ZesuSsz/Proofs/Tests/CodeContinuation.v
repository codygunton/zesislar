Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.

Lemma code_continuation_with_pre `{!islaG Sigma} `{!threadG}
    (sp : bv 64) :
  instr 0x15ce4 (Some a15ce4) -∗
  instr_pre 0x15ce4
    (reg_col zesu_ram_sys_regs ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     instr_pre 0x15ce8
       (reg_col zesu_ram_sys_regs ∗
        "x2" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗ True) ∗ True) ∗ True.
Proof. zesu_block. Qed.

Print Assumptions code_continuation_with_pre.
