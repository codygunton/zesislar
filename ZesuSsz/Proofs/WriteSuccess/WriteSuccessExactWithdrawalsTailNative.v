Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_95 Require Import instrs.

Definition withdrawalTailPost `{!islaG Sigma} `{!threadG}
    (pointer count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (pointer + BV 64 48)%bv ∗
   "x9" ↦ᵣ RVal_Bits (count - BV 64 1)%bv ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalTailPost) := I.
Definition withdrawalTailEntry `{!islaG Sigma} `{!threadG}
    (pointer count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
   "x9" ↦ᵣ RVal_Bits count ∗
   instr_pre 0x15694 (withdrawalTailPost pointer count P) ∗
   instr_pre 0x156e8 (withdrawalTailPost pointer count P) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalTailEntry) := I.

Lemma withdrawal_tail_correct `{!islaG Sigma} `{!threadG}
    pointer count (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_95.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156dc (withdrawalTailEntry pointer count P).
Proof. zesu_block. all: bv_solve. Qed.
Print Assumptions withdrawal_tail_correct.
