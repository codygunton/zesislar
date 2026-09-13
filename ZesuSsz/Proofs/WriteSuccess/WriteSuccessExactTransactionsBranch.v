Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_28 Require Import instrs.

Definition exactTransactionsBranchState `{!islaG Sigma} `{!threadG} (total cursor : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits total ∗ "x11" ↦ᵣ RVal_Bits cursor ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactTransactionsBranchState) := I.

Lemma exact_transactions_branch_correct `{!islaG Sigma} `{!threadG}
    total cursor (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_28.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14f08 (exactTransactionsBranchState total cursor P ∗
    ⌜cursor <> total⌝ ∗ True) -∗
  instr_body 0x15668 (exactTransactionsBranchState total cursor P ∗
    ⌜cursor = total⌝ ∗ True) -∗
  instr_body 0x14f04 (exactTransactionsBranchState total cursor P).
Proof.
  zesu_block.
Qed.
Print Assumptions exact_transactions_branch_correct.

