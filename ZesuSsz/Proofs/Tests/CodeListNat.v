Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.

Lemma code_list_keeps_nat_successor `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (n : nat) :
  ([∗ list] instruction ∈
      take 1 IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15ce4
    (reg_col zesu_ram_sys_regs ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     "x3" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S n))) ∗
     instr_pre 0x15ce8
       (reg_col zesu_ram_sys_regs ∗
        "x2" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
        "x3" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S n))) ∗ True) ∗ True).
Proof. zesu_block. Qed.

Print Assumptions code_list_keeps_nat_successor.
