Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsRegisterGroups.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_copy_call_registers `{!islaG Sigma} `{!threadG} (data : bv 64) :
  reg_col writeSuccessAccessListsOtherRegShapes -∗ "x10" ↦ᵣ RVal_Bits data -∗
  ∃ old_ra : bv 64, "x1" ↦ᵣ RVal_Bits old_ra ∗
    accessRegisterGroup ["x10"; "x12"; "x13"; "x14"; "x15"] ∗
    accessRegisterGroup ["x5"] ∗ accessRegisterGroup accessUnchangedRegisters ∗ True.
Proof. move => *. zesu_block. Qed.
Print Assumptions access_copy_call_registers.
