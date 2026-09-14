Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_89 Require Import instrs.

Definition withdrawalEmptyEntry `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗ reg_col [(KindReg "x18", BitsShape 64)] ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalEmptyEntry) := I.

Definition withdrawalEmptyPost `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗ "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalEmptyPost) := I.

Lemma withdrawal_initial_empty `{!islaG Sigma} `{!threadG} sp (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_89.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156e8 (withdrawalEmptyPost sp P) -∗
  instr_body 0x1568c (withdrawalEmptyEntry sp P).
Proof. zesu_block. Qed.
Print Assumptions withdrawal_initial_empty.

