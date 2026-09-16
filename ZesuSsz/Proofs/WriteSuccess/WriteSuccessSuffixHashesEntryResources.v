Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesSourceWords.

Lemma write_success_suffix_hashes_entry_count_nonzero
    (remaining : nat) (HremainingBound : (S remaining < 2 ^ 64)%nat) :
  Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0.
Proof.
  intro Hzero.
  have HzeroUnsigned := f_equal bv_unsigned Hzero.
  rewrite Z_to_bv_unsigned in HzeroUnsigned.
  have HboundZ :=
    (proj1 (Nat2Z.inj_lt (S remaining) (2 ^ 64))) HremainingBound.
  rewrite Nat2Z.inj_pow in HboundZ.
  have Hrange :
      0 <= Z.of_nat (S remaining) < bv_modulus 64.
  { unfold bv_modulus. cbn. lia. }
  rewrite (bv_wrap_small 64 _ Hrange) in HzeroUnsigned.
  rewrite bv_unsigned_BV in HzeroUnsigned.
  cbn in HzeroUnsigned. lia.
Qed.

Definition writeSuccessSuffixHashesEntryFrame
    `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ: (fun r1 => ⌜valu_has_shape r1 (BitsShape 64)⌝) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ: (fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
   "x11" ↦ᵣ: (fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
   reg_col writeSuccessHashesSourceRest ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗
   base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗ P ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x158e0
     (writeSuccessHashesLoopExit sp base total bytes tail
       ((bv_unsigned sp - 16) ↦ₘ? 16 ∗ P)) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixHashesEntryFrame) := I.

Definition writeSuccessSuffixHashesEntryLoopFrame
    `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessHashesSourceRest ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗
   base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗ P ∗
   writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x158e0
     (writeSuccessHashesLoopExit sp base total bytes tail
       ((bv_unsigned sp - 16) ↦ₘ? 16 ∗ P)) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixHashesEntryLoopFrame) := I.

Definition writeSuccessSuffixHashesEntryPostSpec
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (remaining : nat) (tail : spec)
    (frame : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits value ∗
   "x10" ↦ᵣ: (fun r10 => ⌜valu_has_shape r10 (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessHashesEvents sp (S remaining) tail)) ∗
   frame ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixHashesEntryPostSpec) := I.
