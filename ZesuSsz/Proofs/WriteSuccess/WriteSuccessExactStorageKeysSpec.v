Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysModel.

(** The loop preserves the complete source array and the caller frame.
    The source bytes determine each payload before execution. *)
Definition writeSuccessExactStorageKeysLoopSpec `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessStorageKeysOtherRegShapes ∗
    "x19" ↦ᵣ RVal_Bits x19 ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x22" ↦ᵣ RVal_Bits pointer ∗
    "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessStorageKeysScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessExactStorageKeysEvents sp processed
      (S remaining) bytes tail) ∗ P ∗
    writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x153b4
      (writeSuccessStorageKeysLoopExit x19 sp base total bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactStorageKeysLoopSpec) := I.
