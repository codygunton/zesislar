(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Export ZesuSsz.Contracts.DecodeItemDomainRanges.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot0000Entries.
#[export] Instance fp_machineAt0000_ForwardA0N0_unfold : LithiumUnfold (@fp_machineAt0000_ForwardA0N0) := I.
#[export] Typeclasses Opaque fp_machineAt0000_ForwardA0N0.
#[export] Instance fp_machineAt0000_ForwardA0N0_intro `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt0000_ForwardA0N0 (args) (returnAddress))
  (∃ (a3 : bv 64) (a4 : bv 64) (a5 : bv 64) (a6 : bv 64) (fp_seed_mstatus_bits : bv 64) (fp_seed_satp : bv 64) (fp_seed_zisk_free_input : bv 64), (reg_col ((decodeItemSysRegs args)) ∗ "x10" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemOutputPointer args))) : bv 64%N)) ∗ "x11" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemInputPointer args))) : bv 64%N)) ∗ "x12" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemInputLength args))) : bv 64%N)) ∗ "x13" ↦ᵣ (RVal_Bits (a3 : bv 64%N)) ∗ "x14" ↦ᵣ (RVal_Bits (a4 : bv 64%N)) ∗ "x15" ↦ᵣ (RVal_Bits (a5 : bv 64%N)) ∗ "x16" ↦ᵣ (RVal_Bits (a6 : bv 64%N)) ∗ "x2" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemStackPointer args))) : bv 64%N)) ∗ "x1" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (decodeItemReturnAddress args))) : bv 64%N)) ∗ "x8" ↦ᵣ (RVal_Bits ((decodeItemSavedFramePointer args) : bv 64%N)) ∗ (decodeItemInputPointer args) ↦ₘ∗ (decodeItemInputBytes args) ∗ (decodeItemOutputPointer args) ↦ₘ∗ (decodeItemBeforeStorage args) ∗ (((decodeItemStackPointer args - decodeItemStackBytes))%Z) ↦ₘ? (decodeItemStackBytes) ∗ ⌜(decodeItemDomainAt returnAddress decodeItemC1BDomain args)⌝ ∗ ⌜((bv_unsigned (Z_to_bv 64 (decodeItemReturnAddress args)) mod 4 = 0)%Z)⌝ ∗ True ∗ ⌜((bool_decide ((bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z)) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z))) = (0%Z))%Z))⌝))%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance fp_machineAt0000_unfold : LithiumUnfold (@fp_machineAt0000) := I.
#[export] Typeclasses Opaque fp_machineAt0000.
#[export] Instance fp_machineAt0000_intro `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt0000 (args) (returnAddress) (K))
  (fp_machineAt0000_ForwardA0N0 (args) (returnAddress) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

