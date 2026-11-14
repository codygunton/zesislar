(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Export ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Export ZesuSsz.Compliance.ParentHeaderHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot5cb8Entries.
#[export] Instance fp_machineAt5cb8_ForwardA0N0_unfold : LithiumUnfold (@fp_machineAt5cb8_ForwardA0N0) := I.
#[export] Typeclasses Opaque fp_machineAt5cb8_ForwardA0N0.
#[export] Instance fp_machineAt5cb8_ForwardA0N0_intro `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt5cb8_ForwardA0N0 (args) (returnAddress))
  (∃ (x5 : bv 64) (x6 : bv 64) (x7 : bv 64) (x13 : bv 64) (x14 : bv 64) (x15 : bv 64) (x16 : bv 64) (x17 : bv 64) (x28 : bv 64) (x29 : bv 64) (x30 : bv 64) (x31 : bv 64) (fp_seed_mstatus_bits : bv 64) (fp_seed_satp : bv 64) (fp_seed_zisk_free_input : bv 64), (reg_col ((parentHeaderSysRegs args)) ∗ "x1" ↦ᵣ (RVal_Bits ((parentHeaderReturnAddress args) : bv 64%N)) ∗ "x2" ↦ᵣ (RVal_Bits ((parentHeaderStackPointer args) : bv 64%N)) ∗ "x5" ↦ᵣ (RVal_Bits (x5 : bv 64%N)) ∗ "x6" ↦ᵣ (RVal_Bits (x6 : bv 64%N)) ∗ "x7" ↦ᵣ (RVal_Bits (x7 : bv 64%N)) ∗ "x8" ↦ᵣ (RVal_Bits ((parentHeaderSavedX8 args) : bv 64%N)) ∗ "x9" ↦ᵣ (RVal_Bits ((parentHeaderSavedX9 args) : bv 64%N)) ∗ "x10" ↦ᵣ (RVal_Bits ((parentHeaderResultPointer args) : bv 64%N)) ∗ "x11" ↦ᵣ (RVal_Bits ((parentHeaderInputPointer args) : bv 64%N)) ∗ "x12" ↦ᵣ (RVal_Bits ((parentHeaderInputLength args) : bv 64%N)) ∗ "x13" ↦ᵣ (RVal_Bits (x13 : bv 64%N)) ∗ "x14" ↦ᵣ (RVal_Bits (x14 : bv 64%N)) ∗ "x15" ↦ᵣ (RVal_Bits (x15 : bv 64%N)) ∗ "x16" ↦ᵣ (RVal_Bits (x16 : bv 64%N)) ∗ "x17" ↦ᵣ (RVal_Bits (x17 : bv 64%N)) ∗ "x18" ↦ᵣ (RVal_Bits ((parentHeaderSavedX18 args) : bv 64%N)) ∗ "x19" ↦ᵣ (RVal_Bits ((parentHeaderSavedX19 args) : bv 64%N)) ∗ "x20" ↦ᵣ (RVal_Bits ((parentHeaderSavedX20 args) : bv 64%N)) ∗ "x21" ↦ᵣ (RVal_Bits ((parentHeaderSavedX21 args) : bv 64%N)) ∗ "x22" ↦ᵣ (RVal_Bits ((parentHeaderSavedX22 args) : bv 64%N)) ∗ "x23" ↦ᵣ (RVal_Bits ((parentHeaderSavedX23 args) : bv 64%N)) ∗ "x24" ↦ᵣ (RVal_Bits ((parentHeaderSavedX24 args) : bv 64%N)) ∗ "x25" ↦ᵣ (RVal_Bits ((parentHeaderSavedX25 args) : bv 64%N)) ∗ "x26" ↦ᵣ (RVal_Bits ((parentHeaderSavedX26 args) : bv 64%N)) ∗ "x27" ↦ᵣ (RVal_Bits ((parentHeaderSavedX27 args) : bv 64%N)) ∗ "x28" ↦ᵣ (RVal_Bits (x28 : bv 64%N)) ∗ "x29" ↦ᵣ (RVal_Bits (x29 : bv 64%N)) ∗ "x30" ↦ᵣ (RVal_Bits (x30 : bv 64%N)) ∗ "x31" ↦ᵣ (RVal_Bits (x31 : bv 64%N)) ∗ (bv_unsigned (parentHeaderInputPointer args)) ↦ₘ∗ (parentHeaderInputBytes args) ∗ (bv_unsigned (parentHeaderResultPointer args)) ↦ₘ? (parentHeaderResultSize) ∗ (((bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes))%Z) ↦ₘ? (parentHeaderStackBytes) ∗ (((bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes -
      parentHeaderCalleeBytes))%Z) ↦ₘ? (parentHeaderCalleeBytes) ∗ (parentHeaderMemcpySource) ↦ₘ∗ (parentHeaderMemcpySourceBefore args) ∗ (ziskExtraParamsAddress) ↦ₘ∗ (parentHeaderMemcpyScratchBefore args) ∗ ⌜(bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args)⌝ ∗ ⌜((bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0)%Z)⌝ ∗ True ∗ ⌜((bool_decide ((bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z)) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z))) = (0%Z))%Z))⌝))%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance fp_machineAt5cb8_unfold : LithiumUnfold (@fp_machineAt5cb8) := I.
#[export] Typeclasses Opaque fp_machineAt5cb8.
#[export] Instance fp_machineAt5cb8_intro `{!islaG Sigma} `{!threadG} (args : ParentHeaderArgs) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt5cb8 (args) (returnAddress) (K))
  (fp_machineAt5cb8_ForwardA0N0 (args) (returnAddress) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

