Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import isla.riscv64.riscv64.

Lemma storage_registers_access_return `{!islaG Sigma} `{!threadG} :
  reg_col writeSuccessStorageKeysOtherRegShapes -∗
  ∃ data index : bv 64, reg_col writeSuccessAccessListsOtherRegShapes ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits index ∗ True.
Proof. move => *. zesu_block. Qed.
Print Assumptions storage_registers_access_return.
