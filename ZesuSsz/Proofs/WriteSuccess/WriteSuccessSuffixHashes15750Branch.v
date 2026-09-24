Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTactics.

Definition writeSuccessSuffixHashes15750NonzeroState
    `{!islaG Sigma} `{!threadG} (value : bv 64) (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits value ∗ Q)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixHashes15750NonzeroState) := I.

Definition writeSuccessSuffixHashes15750ZeroState
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ Q)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixHashes15750ZeroState) := I.

Lemma write_success_suffix_hashes_15750_nonzero_state
    `{!islaG Sigma} `{!threadG} (value : bv 64) (Q : iProp Sigma)
    (Hvalue : value <> BV 64 0) :
  instr 0x15750 (Some IslaTraces.write_success_102.a15750.a15750) -∗
  instr_pre 0x15754
    (writeSuccessSuffixHashes15750NonzeroState value Q) -∗
  instr_body 0x15750
    (writeSuccessSuffixHashes15750NonzeroState value Q).
Proof. move => *. zesu_block. Qed.

Lemma write_success_suffix_hashes_15750_zero_state
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr 0x15750 (Some IslaTraces.write_success_102.a15750.a15750) -∗
  instr_pre 0x158e0
    (writeSuccessSuffixHashes15750ZeroState Q) -∗
  instr_body 0x15750
    (writeSuccessSuffixHashes15750ZeroState Q).
Proof. move => *. zesu_block. Qed.
