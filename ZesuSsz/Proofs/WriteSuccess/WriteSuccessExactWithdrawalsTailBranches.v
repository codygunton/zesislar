Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsTailNative.
From IslaTraces.write_success_95 Require Import instrs.

Definition withdrawalTailHeadPost `{!islaG Sigma} `{!threadG}
    (pointer count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (withdrawalTailPost pointer count P ∗ ⌜(count - BV 64 1)%bv <> BV 64 0⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalTailHeadPost) := I.
Definition withdrawalTailExitPost `{!islaG Sigma} `{!threadG}
    (pointer count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (withdrawalTailPost pointer count P ∗ ⌜(count - BV 64 1)%bv = BV 64 0⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalTailExitPost) := I.
Definition withdrawalTailBranchesEntry `{!islaG Sigma} `{!threadG}
    (pointer count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits pointer ∗ "x9" ↦ᵣ RVal_Bits count ∗
   instr_pre 0x15694 (withdrawalTailHeadPost pointer count P) ∗
   instr_pre 0x156e8 (withdrawalTailExitPost pointer count P) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalTailBranchesEntry) := I.

Lemma withdrawal_tail_branches_correct `{!islaG Sigma} `{!threadG}
    pointer count (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_95.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156dc (withdrawalTailBranchesEntry pointer count P).
Proof.
  zesu_block.
  all: have Hdecrement : (count - BV 64 1)%bv =
    (count + BV 64 18446744073709551615)%bv by bv_solve.
  all: rewrite Hdecrement; assumption.
Qed.
Print Assumptions withdrawal_tail_branches_correct.
