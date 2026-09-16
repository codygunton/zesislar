Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Import ListNotations.

Lemma write_success_suffix_ram_lower_904 (sp : bv 64)
    (Hmin : (mapRamBase defaultMap) <= bv_unsigned sp)
    (Haddr : bv_unsigned (sp + BV 64 904)%bv = bv_unsigned sp + 904) :
    bv_unsigned (sp + BV 64 904)%bv >= bv_unsigned (BV 64 (mapRamBase defaultMap)).
Proof.
  rewrite Haddr bv_unsigned_BV. lia.
Qed.

Lemma write_success_suffix_ram_lower_912 (sp : bv 64)
    (Hmin : (mapRamBase defaultMap) <= bv_unsigned sp)
    (Haddr : bv_unsigned (sp + BV 64 912)%bv = bv_unsigned sp + 912) :
    bv_unsigned (sp + BV 64 912)%bv >= bv_unsigned (BV 64 (mapRamBase defaultMap)).
Proof.
  rewrite Haddr bv_unsigned_BV. lia.
Qed.

Lemma write_success_suffix_ram_upper_904 (sp : bv 64)
    (Hmax : bv_unsigned sp + 1896 < (machineRamEnd defaultMap))
    (Haddr : bv_unsigned (sp + BV 64 904)%bv = bv_unsigned sp + 904) :
    bv_unsigned (sp + BV 64 904)%bv <=
      bv_unsigned (BV 64 (mapRamBase defaultMap) + BV 64 (mapRamSize defaultMap) - BV 64 8)%bv.
Proof. clear - Hmax Haddr. rewrite Haddr. bv_solve. Qed.

Lemma write_success_suffix_ram_upper_912 (sp : bv 64)
    (Hmax : bv_unsigned sp + 1896 < (machineRamEnd defaultMap))
    (Haddr : bv_unsigned (sp + BV 64 912)%bv = bv_unsigned sp + 912) :
    bv_unsigned (sp + BV 64 912)%bv <=
      bv_unsigned (BV 64 (mapRamBase defaultMap) + BV 64 (mapRamSize defaultMap) - BV 64 8)%bv.
Proof. clear - Hmax Haddr. rewrite Haddr. bv_solve. Qed.

Definition writeSuccessSuffixHashesEntrySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
    (bv_unsigned sp + 904) ↦ₘ pointer ∗
    (bv_unsigned sp + 912) ↦ₘ Z_to_bv 64 (Z.of_nat (S remaining)) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessHashesEvents sp (S remaining) tail)) ∗
    P ∗ writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x158e0
      (writeSuccessHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashesEntrySpec) := I.

Definition writeSuccessSuffixHashes15740Post
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessHashesOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗
   base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
   (bv_unsigned sp + 904) ↦ₘ pointer ∗
   (bv_unsigned sp + 912) ↦ₘ Z_to_bv 64 (Z.of_nat (S remaining)) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessHashesEvents sp (S remaining) tail)) ∗
   P ∗ writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x158e0
     (writeSuccessHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15740Post) := I.

Definition writeSuccessSuffixHashesAt15740Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
    (bv_unsigned sp + 904) ↦ₘ pointer ∗
    (bv_unsigned sp + 912) ↦ₘ Z_to_bv 64 (Z.of_nat (S remaining)) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessHashesEvents sp (S remaining) tail)) ∗
    P ∗ writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x15744
      (writeSuccessSuffixHashes15740Post P sp pointer base total processed
        remaining bytes tail) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashesAt15740Spec) := I.

Definition writeSuccessSuffixHashes15740Frame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) : iProp Sigma :=
  (reg_col writeSuccessHashesOtherRegShapes ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗ base ↦ₘ∗ bytes ∗
   writeSuccessHashesScratch sp ∗
   (bv_unsigned sp + 904) ↦ₘ pointer ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessHashesEvents sp (S remaining) tail)) ∗
   P ∗ writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x15744
     (writeSuccessSuffixHashes15740Post P sp pointer base total processed
       remaining bytes tail) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15740Frame) := I.

Definition writeSuccessSuffixHashes15740State
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ: (fun _ => True) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   bv_unsigned (sp + BV 64 912)%bv ↦ₘ
     Z_to_bv 64 (Z.of_nat (S remaining)) ∗
   ⌜bv_extract 0 3 (sp + BV 64 912)%bv = BV 3 0⌝ ∗
   ⌜bv_unsigned (sp + BV 64 912)%bv >= bv_unsigned (BV 64 (mapRamBase defaultMap))⌝ ∗
   ⌜bv_unsigned (sp + BV 64 912)%bv <=
     bv_unsigned (BV 64 (mapRamBase defaultMap) + BV 64 (mapRamSize defaultMap) - BV 64 8)%bv⌝ ∗
   writeSuccessSuffixHashes15740Frame P sp pointer base total processed
     remaining bytes tail)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15740State) := I.

Definition writeSuccessSuffixHashes15740Result
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   bv_unsigned (sp + BV 64 912)%bv ↦ₘ
     Z_to_bv 64 (Z.of_nat (S remaining)) ∗
   writeSuccessSuffixHashes15740Frame P sp pointer base total processed
     remaining bytes tail)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15740Result) := I.
