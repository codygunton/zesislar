Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.

Definition writeSuccessTransactionsPost15690ZeroSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗
   instr_pre (pc + 88)
     (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗ True))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15690ZeroSpec) := I.

Lemma write_success_transactions_zero_bv :
  Z_to_bv 64 (Z.of_nat 0) = BV 64 0.
Proof. bv_solve. Qed.

Lemma write_success_transactions_post_15690_zero_spec
    `{!islaG Sigma} `{!threadG} :
  instr 0x15690 (Some IslaTraces.write_success_89.a15690.a15690) -∗
  instr_body 0x15690 (writeSuccessTransactionsPost15690ZeroSpec 0x15690).
Proof. move => *. zesu_block. Qed.

Lemma write_success_transactions_post_15690_zero
    `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x156e8
    (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗ True) -∗
  instr_body 0x15690
    (reg_col zesu_ram_sys_regs ∗ "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗ True).
Proof. move => *. zesu_block. Qed.
