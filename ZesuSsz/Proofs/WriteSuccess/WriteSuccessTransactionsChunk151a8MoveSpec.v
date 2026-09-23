Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Export IslaTraces.write_success_49.a151a8.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessTransactions151a8MoveSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  (∃ value : bv 64,
    reg_col zesu_ram_sys_regs ∗
    ("x13" ↦ᵣ: fun _ => True) ∗
    "x21" ↦ᵣ RVal_Bits value ∗
    instr_pre (pc + 4)
      (reg_col zesu_ram_sys_regs ∗
       "x13" ↦ᵣ RVal_Bits value ∗
       "x21" ↦ᵣ RVal_Bits value ∗ True))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions151a8MoveSpec) := I.

Lemma write_success_transactions_151a8_move_spec
    `{!islaG Sigma} `{!threadG} (pc : Z) :
  instr pc (Some a151a8) ⊢
  instr_body pc (writeSuccessTransactions151a8MoveSpec pc).
Proof. move => *. zesu_block. Qed.
