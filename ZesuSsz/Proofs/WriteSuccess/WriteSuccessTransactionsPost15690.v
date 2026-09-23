Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.

Definition writeSuccessTransactionsPost15690BranchSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  (∃ data : bv 64,
    reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits data ∗
    instr_pre (pc + 88)
      (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits data ∗ True) ∗
    instr_pre (pc + 4)
      (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits data ∗ True))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15690BranchSpec) := I.

Definition writeSuccessTransactionsPost15690NonzeroSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  (∃ data : bv 64,
    reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits data ∗
    ⌜data <> BV 64 0⌝ ∗
    instr_pre (pc + 4)
      (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits data ∗ True))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15690NonzeroSpec) := I.

Lemma write_success_transactions_post_15690_nonzero_spec
    `{!islaG Sigma} `{!threadG} :
  instr 0x15690 (Some IslaTraces.write_success_89.a15690.a15690) -∗
  instr_body 0x15690 (writeSuccessTransactionsPost15690NonzeroSpec 0x15690).
Proof. move => *. zesu_block. Qed.

Lemma write_success_transactions_post_15690_branch_spec
    `{!islaG Sigma} `{!threadG} :
  instr 0x15690 (Some IslaTraces.write_success_89.a15690.a15690) -∗
  instr_body 0x15690 (writeSuccessTransactionsPost15690BranchSpec 0x15690).
Proof. move => *. zesu_block. Qed.

Lemma write_success_transactions_post_15690_branch
    `{!islaG Sigma} `{!threadG} (data : bv 64) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x156e8
    (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits data ∗ True) -∗
  instr_pre 0x15694
    (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits data ∗ True) -∗
  instr_body 0x15690
    (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits data ∗ True).
Proof. move => *. zesu_block. Qed.
