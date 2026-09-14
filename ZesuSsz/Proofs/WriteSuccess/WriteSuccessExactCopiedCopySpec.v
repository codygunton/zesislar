Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import Interfaces WriteSuccessExactNativeLoadSpec.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessExactCopiedNativeLoadSpec WriteSuccessPrologueSpec.
Definition exactNativeCopiedCopyPost `{!islaG Sigma} `{!threadG}
    (stage : nat) (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64) (object : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  exactNativeCopiedLoadState stage (sp - BV 64 2000)%bv decoded object
    (((bv_unsigned (sp - BV 64 2000)%bv) + 312) ↦ₘ∗ take 720 object ∗
     ((bv_unsigned (sp - BV 64 2000)%bv) + 1032) ↦ₘ? 864 ∗
     writeSuccessSavedSlots sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P).
Global Instance : LithiumUnfold (@exactNativeCopiedCopyPost) := I.
