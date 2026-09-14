Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessExactNativeLoadSpec WriteSuccessPostTransactionResources.
Import ListNotations.
Open Scope Z_scope.

Definition exactNativeCopiedWordOffsets : list (nat * Z) :=
  [(0%nat, 24); (1%nat, 16); (2%nat, 40); (3%nat, 32);
   (4%nat, 56); (5%nat, 48); (6%nat, 64); (7%nat, 72);
   (8%nat, 8); (9%nat, 80); (10%nat, 296); (11%nat, 304);
   (12%nat, 280); (13%nat, 288); (14%nat, 96); (15%nat, 88)].

Definition exactNativeCopiedWords `{!islaG Sigma}
    (stage : nat) (sp : bv 64) (object : list (bv 8)) : iProp Sigma :=
  if decide (stage = 16%nat) then writeSuccessExactCopiedTailWords sp object else
  ([∗ list] binding ∈ take stage exactNativeCopiedWordOffsets,
    (bv_unsigned sp + binding.2) ↦ₘ
      writeSuccessPostWord (writeSuccessPostTailWords object) binding.1)%I.
Global Instance : LithiumUnfold (@exactNativeCopiedWords) := I.

Definition exactNativeCopiedFree `{!islaG Sigma}
    (stage : nat) (sp : bv 64) : iProp Sigma :=
  match stage with
  | 0%nat => bv_unsigned sp ↦ₘ? 312
  | 4%nat => bv_unsigned sp ↦ₘ? 16 ∗ (bv_unsigned sp + 48) ↦ₘ? 264
  | 8%nat => bv_unsigned sp ↦ₘ? 16 ∗ (bv_unsigned sp + 80) ↦ₘ? 232
  | 10%nat => bv_unsigned sp ↦ₘ? 8 ∗ (bv_unsigned sp + 88) ↦ₘ? 224
  | 16%nat => bv_unsigned sp ↦ₘ? 8 ∗ (bv_unsigned sp + 104) ↦ₘ? 176
  | _ => False
  end%I.
Global Instance : LithiumUnfold (@exactNativeCopiedFree) := I.

Definition exactNativeCopiedLoadRegisters `{!islaG Sigma} `{!threadG}
    (stage : nat) (object : list (bv 8)) : iProp Sigma :=
  if decide (stage = 10%nat) then
    (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
       filter (fun register => bool_decide (register ∉ ["x10"; "x11"; "x12"; "x13"]))
         exactNativeLoadOtherRegisters) ∗
     "x10" ↦ᵣ RVal_Bits (writeSuccessPostWord (writeSuccessPostTailWords object) 10) ∗
     "x11" ↦ᵣ RVal_Bits (writeSuccessPostWord (writeSuccessPostTailWords object) 11) ∗
     "x12" ↦ᵣ RVal_Bits (writeSuccessPostWord (writeSuccessPostTailWords object) 12) ∗
     "x13" ↦ᵣ RVal_Bits (writeSuccessPostWord (writeSuccessPostTailWords object) 13))%I
  else reg_col exactNativeLoadOtherShapes.
Global Instance : LithiumUnfold (@exactNativeCopiedLoadRegisters) := I.

Definition exactNativeCopiedLoadState `{!islaG Sigma} `{!threadG}
    (stage : nat) (sp decoded : bv 64) (object : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ exactNativeCopiedLoadRegisters stage object ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits decoded ∗
   bv_unsigned decoded ↦ₘ∗ object ∗
   exactNativeCopiedFree stage sp ∗ exactNativeCopiedWords stage sp object ∗
   ⌜length object = 848%nat⌝ ∗ ⌜bv_unsigned decoded `mod` 8 = 0⌝ ∗
   ⌜mapRamBase defaultMap <= bv_unsigned decoded⌝ ∗
   ⌜bv_unsigned decoded + 848 < machineRamEnd defaultMap⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜mapRamBase defaultMap <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 312 < machineRamEnd defaultMap⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactNativeCopiedLoadState) := I.
