Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsRecipientBranch.
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

Definition State_15194
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (tag : bv 64) (first : bv 64) (second : bv 64) (w0 : bv 64) (w1 : bv 64) (w2 : bv 64) (w3 : bv 64) (oldra : bv 64) (old5 : bv 64) (old11 : bv 64) (old12 : bv 64) (old13 : bv 64) (last : bv 32) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ n : bv 64,
   ∃ b : bv 64,
   ∃ b0 : bv 64,
   ("x1" ↦ᵣ RVal_Bits oldra) ∗
   ("x5" ↦ᵣ RVal_Bits old5) ∗
   ("x11" ↦ᵣ RVal_Bits old11) ∗
   ("x12" ↦ᵣ RVal_Bits old12) ∗
   ("x13" ↦ᵣ RVal_Bits old13) ∗
   ("x18" ↦ᵣ RVal_Bits w0) ∗
   ("x20" ↦ᵣ RVal_Bits w1) ∗
   ((bv_unsigned sp + 128) ↦ₘ w2) ∗
   ("x21" ↦ᵣ RVal_Bits w3) ∗
   ((bv_unsigned sp + 1640) ↦ₘ first) ∗
   ((bv_unsigned sp + 1648) ↦ₘ second) ∗
   ((bv_unsigned sp + 1656) ↦ₘ last) ∗
   ((bv_unsigned sp + 1744) ↦ₘ? 20) ∗
   ((bv_unsigned sp - 48) ↦ₘ? 48) ∗
   (spec_trace (transactionRecipientValueTrace sp 0 first second w0 w1 w2 w3 last tail)) ∗
   (P) ∗
   ("x2" ↦ᵣ RVal_Bits sp) ∗
   ((bv_unsigned sp + 120) ↦ₘ (BV 64 0)) ∗
   (reg_col zesu_ram_sys_regs) ∗
   ("x10" ↦ᵣ RVal_Bits (BV 64 0)) ∗
   (mmio_range (604086456 + 8) 16) ∗
   (⌜(bv_unsigned sp `mod` 8 = 0)%Z⌝) ∗
   (⌜(0 ≤ bv_unsigned sp)%Z⌝) ∗
   (⌜(bv_unsigned sp + 128 < 0 + 1073741824)%Z⌝) ∗
   (⌜(bv_unsigned sp `mod` 16 = 0)%Z⌝) ∗
   (⌜(0 ≤ bv_unsigned sp - 48)%Z⌝) ∗
   (⌜(bv_unsigned sp + 1764 < 0 + 1073741824)%Z⌝) ∗
   (⌜(Z.land (bv_unsigned b) 131072 = 0)%Z⌝) ∗
   (⌜(Z.land (bvn_unsigned n) 131072 = 0)%Z⌝) ∗
   (⌜(Z.land (bv_unsigned b0) 131072 = 0)%Z⌝) ∗
   (⌜(-1 < bv_unsigned b0 < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed b0 < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned b < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed b < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned n < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed n < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned last < bv_modulus 32)%Z⌝) ∗
   (⌜(32%N ≠ 0%N → - bv_half_modulus 32 ≤ bv_signed last < bv_half_modulus 32)%Z⌝) ∗
   (⌜(-1 < bv_unsigned old13 < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed old13 < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned old12 < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed old12 < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned old11 < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed old11 < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned old5 < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed old5 < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned oldra < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed oldra < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned w3 < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed w3 < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned w2 < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed w2 < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned w1 < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed w1 < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned w0 < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed w0 < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned second < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed second < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned first < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed first < bv_half_modulus 64)%Z⌝) ∗
   (⌜(-1 < bv_unsigned sp < bv_modulus 64)%Z⌝) ∗
   (⌜(64%N ≠ 0%N → - bv_half_modulus 64 ≤ bv_signed sp < bv_half_modulus 64)%Z⌝) ∗
   True)%I.
Global Instance : LithiumUnfold (@State_15194) := I.
Global Typeclasses Opaque State_15194.
