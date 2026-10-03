Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsPriority.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAuthorizationsInt.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsInt.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8Defs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Automation.WordPayloads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLimitCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsRecipientBranchHandoff.

Definition State_1511c
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (low : bv 64) (high : bv 64) (tag : bv 64) (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ b : bv 64,
   ("x2" ↦ᵣ RVal_Bits sp) ∗
   ("x1" ↦ᵣ RVal_Bits (BV 64 86296)) ∗
   ("x5" ↦ᵣ RVal_Bits (BV 64 604086456)) ∗
   ("x10" ↦ᵣ RVal_Bits (sp - 32)%bv) ∗
   ("x11" ↦ᵣ RVal_Bits (BV 64 16)) ∗
   ((bv_unsigned sp - 32) ↦ₘ? 32) ∗
   (spec_trace trace) ∗
   ("x24" ↦ᵣ RVal_Bits high) ∗
   ("x25" ↦ᵣ RVal_Bits low) ∗
   (P) ∗
   (reg_col zesu_ram_sys_regs) ∗
   ("x27" ↦ᵣ RVal_Bits tag) ∗
   (mmio_range (604086456 + 8) 16) ∗
   (⌜(bv_unsigned sp `mod` 16 = 0)%Z⌝) ∗
   (⌜(0 ≤ bv_unsigned sp - 32)%Z⌝) ∗
   (⌜(bv_unsigned sp < 0 + 1073741824)%Z⌝) ∗
   (⌜(Z.land (bv_unsigned b) 131072 = 0)%Z⌝) ∗
   (⌜(tag ≠ 0%bv)%Z⌝) ∗
   (⌜(-1 < bv_unsigned b < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed b < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned tag < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed tag < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned high < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed high < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned low < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed low < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned sp < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed sp < bv_half_modulus 64)%Z⌝) ∗
   True)%I.
Global Instance : LithiumUnfold (@State_1511c) := I.
Global Typeclasses Opaque State_1511c.
