(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.BerlinGasCalcContract.
Require Export ZesuSsz.Compliance.BerlinGasCalcHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import ZesuSsz.Generated.BerlinGasCalc.FP301.Pilot39a4Entries.
#[export] Instance fp_machineAt39a4_ForwardA0N0_unfold : LithiumUnfold (@fp_machineAt39a4_ForwardA0N0) := I.
#[export] Typeclasses Opaque fp_machineAt39a4_ForwardA0N0.
#[export] Instance fp_machineAt39a4_ForwardA0N0_intro `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt39a4_ForwardA0N0 (args) (returnAddress))
  (∃ (x5 : bv 64) (x6 : bv 64) (x7 : bv 64) (x17 : bv 64) (x28 : bv 64) (fp_seed_mstatus_bits : bv 64) (fp_seed_satp : bv 64) (fp_seed_zisk_input_end : bv 64) (fp_seed_zisk_free_input : bv 64), (reg_col (zesu_sys_regs) ∗ "x1" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (berlinReturnAddress args))) : bv 64%N)) ∗ "x2" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (berlinStackPointer args))) : bv 64%N)) ∗ "x8" ↦ᵣ (RVal_Bits ((berlinSavedFramePointer args) : bv 64%N)) ∗ "x10" ↦ᵣ (RVal_Bits ((berlinBaseLength args) : bv 64%N)) ∗ "x11" ↦ᵣ (RVal_Bits ((berlinExponentLength args) : bv 64%N)) ∗ "x12" ↦ᵣ (RVal_Bits ((berlinModulusLength args) : bv 64%N)) ∗ "x13" ↦ᵣ (RVal_Bits ((berlinExponentHead0 args) : bv 64%N)) ∗ "x14" ↦ᵣ (RVal_Bits ((berlinExponentHead1 args) : bv 64%N)) ∗ "x15" ↦ᵣ (RVal_Bits ((berlinExponentHead2 args) : bv 64%N)) ∗ "x16" ↦ᵣ (RVal_Bits ((berlinExponentHead3 args) : bv 64%N)) ∗ "x5" ↦ᵣ (RVal_Bits (x5 : bv 64%N)) ∗ "x6" ↦ᵣ (RVal_Bits (x6 : bv 64%N)) ∗ "x7" ↦ᵣ (RVal_Bits (x7 : bv 64%N)) ∗ "x17" ↦ᵣ (RVal_Bits (x17 : bv 64%N)) ∗ "x28" ↦ᵣ (RVal_Bits (x28 : bv 64%N)) ∗ (((berlinStackPointer args - berlinGasCalcStackBytes))%Z) ↦ₘ? (berlinGasCalcStackBytes) ∗ ⌜(berlinGasCalcDomainAt returnAddress args)⌝ ∗ ⌜((bv_unsigned (Z_to_bv 64 (berlinReturnAddress args)) mod 4 = 0)%Z)⌝ ∗ True ∗ ⌜((bool_decide ((bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z)) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z))) = (0%Z))%Z))⌝))%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance fp_machineAt39a4_unfold : LithiumUnfold (@fp_machineAt39a4) := I.
#[export] Typeclasses Opaque fp_machineAt39a4.
#[export] Instance fp_machineAt39a4_intro `{!islaG Sigma} `{!threadG} (args : BerlinGasCalcArgs) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt39a4 (args) (returnAddress) (K))
  (fp_machineAt39a4_ForwardA0N0 (args) (returnAddress) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

