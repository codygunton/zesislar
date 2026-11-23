(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceBlockEntries.
Require Export ZesuSsz.Compliance.KeysToOwnedSliceHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import ZesuSsz.Automation2.Hist.
Require Import ZesuSsz.Generated.KeysToOwnedSlice.FP301.Pilot0078Entries.
#[export] Typeclasses Opaque fp_machineAt0078_ForwardA0N0_Hist.
#[export] Instance fp_machineAt0078_ForwardA0N0_unfold : LithiumUnfold (@fp_machineAt0078_ForwardA0N0) := I.
#[export] Typeclasses Opaque fp_machineAt0078_ForwardA0N0.
#[export] Instance fp_machineAt0078_ForwardA0N0_intro `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt0078_ForwardA0N0 (args) (returnAddress))
  (∃ (x5 : bv 64) (x6 : bv 64) (x7 : bv 64) (x13 : bv 64) (x14 : bv 64) (x15 : bv 64) (x16 : bv 64) (x17 : bv 64) (x28 : bv 64) (x29 : bv 64) (x30 : bv 64) (x31 : bv 64), (reg_col (zesu_sys_regs) ∗ "x1" ↦ᵣ (RVal_Bits ((keysReturnAddress args) : bv 64%N)) ∗ "x2" ↦ᵣ (RVal_Bits ((bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) : bv 64%N)) ∗ "x5" ↦ᵣ (RVal_Bits (x5 : bv 64%N)) ∗ "x6" ↦ᵣ (RVal_Bits (x6 : bv 64%N)) ∗ "x7" ↦ᵣ (RVal_Bits (x7 : bv 64%N)) ∗ "x8" ↦ᵣ (RVal_Bits ((bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 96%Z)) : bv 64%N)) ∗ "x9" ↦ᵣ (RVal_Bits ((keysResultPointer args) : bv 64%N)) ∗ "x10" ↦ᵣ (RVal_Bits ((keysResultPointer args) : bv 64%N)) ∗ "x11" ↦ᵣ (RVal_Bits ((keysListPointer args) : bv 64%N)) ∗ "x12" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (arrayListCapacity (keysBlockList args)))) : bv 64%N)) ∗ "x13" ↦ᵣ (RVal_Bits (x13 : bv 64%N)) ∗ "x14" ↦ᵣ (RVal_Bits (x14 : bv 64%N)) ∗ "x15" ↦ᵣ (RVal_Bits (x15 : bv 64%N)) ∗ "x16" ↦ᵣ (RVal_Bits (x16 : bv 64%N)) ∗ "x17" ↦ᵣ (RVal_Bits (x17 : bv 64%N)) ∗ "x18" ↦ᵣ (RVal_Bits ((keysListPointer args) : bv 64%N)) ∗ "x19" ↦ᵣ (RVal_Bits ((keysReturnAddress args) : bv 64%N)) ∗ "x20" ↦ᵣ (RVal_Bits ((keysAllocatorPointer args) : bv 64%N)) ∗ "x21" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (toOwnedAllocatorContext (keysBase args)))) : bv 64%N)) ∗ "x22" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (arrayListPointer (keysBlockList args)))) : bv 64%N)) ∗ "x23" ↦ᵣ (RVal_Bits (((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) : bv 64%N)) ∗ "x24" ↦ᵣ (RVal_Bits ((BV 64%N 2148611800%Z) : bv 64%N)) ∗ "x25" ↦ᵣ (RVal_Bits ((keysSavedX25 args) : bv 64%N)) ∗ "x26" ↦ᵣ (RVal_Bits ((keysSavedX26 args) : bv 64%N)) ∗ "x27" ↦ᵣ (RVal_Bits ((keysSavedX27 args) : bv 64%N)) ∗ "x28" ↦ᵣ (RVal_Bits (x28 : bv 64%N)) ∗ "x29" ↦ᵣ (RVal_Bits (x29 : bv 64%N)) ∗ "x30" ↦ᵣ (RVal_Bits (x30 : bv 64%N)) ∗ "x31" ↦ᵣ (RVal_Bits (x31 : bv 64%N)) ∗ (bv_unsigned (keysListPointer args)) ↦ₘ∗ (arrayListHeaderBytes (keysBlockList args)) ∗ (arrayListPointer (keysBlockList args)) ↦ₘ∗ (arrayListItems (keysBlockList args)) ∗ (((arrayListPointer (keysBlockList args) +
      arrayListLength (keysBlockList args) * keysElementBytes))%Z) ↦ₘ? (((arrayListCapacity (keysBlockList args) - arrayListLength (keysBlockList args)) *
        keysElementBytes)) ∗ ZesuSsz.Contracts.AltFlAllocPremises.altFlBlock ((arrayListPointer (keysBlockList args))) ((arrayListCapacity (keysBlockList args) * keysElementBytes)) (keysLog2Alignment) ∗ (bv_unsigned (keysResultPointer args)) ↦ₘ∗ (toOwnedResultBefore (keysBase args)) ∗ (bv_unsigned (keysAllocatorPointer args)) ↦ₘ∗ (altFlAllocatorBytes (toOwnedAllocatorContext (keysBase args))) ∗ (sym_alt_fl_alloc_vtable) ↦ₘ∗ (altFlVtableBytes) ∗ ZesuSsz.Contracts.AltFlAllocPremises.altFlHeap ∗ (ziskExtraParamsAddress) ↦ₘ∗ (toOwnedScratchBefore (keysBase args)) ∗ (((bv_unsigned (keysStackPointer args) - keysBlockFrameBytes))%Z) ↦ₘ? (keysBlockScratchBytes) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 16%Z))) ↦ₘ (keysSavedX24 args) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 24%Z))) ↦ₘ (keysSavedX23 args) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 32%Z))) ↦ₘ (keysSavedX22 args) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 40%Z))) ↦ₘ (keysSavedX21 args) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 48%Z))) ↦ₘ (keysSavedX20 args) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 56%Z))) ↦ₘ (keysSavedX19 args) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 64%Z))) ↦ₘ (keysSavedX18 args) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 72%Z))) ↦ₘ (keysSavedX9 args) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 80%Z))) ↦ₘ (keysSavedX8 args) ∗ (bv_unsigned (bv_add (bv_add (keysStackPointer args) (BV 64%N 18446744073709551520%Z)) (BV 64%N 88%Z))) ↦ₘ (keysReturnAddress args) ∗ (((bv_unsigned (keysStackPointer args) - keysBlockFrameBytes - keysBlockCalleeBytes))%Z) ↦ₘ? (keysBlockCalleeBytes) ∗ ⌜(keysBlockDomainAt returnAddress args)⌝ ∗ ⌜((bv_unsigned (keysReturnAddress args) mod 4 = 0)%Z)⌝ ∗ ⌜((bool_decide (((Z_to_bv 64%N (arrayListLength (keysBlockList args)))) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned ((Z_to_bv 64%N (arrayListLength (keysBlockList args))))) = (0%Z))%Z))⌝ ∗ ⌜zesu_hist (fp_machineAt0078_ForwardA0N0_Hist (args) (returnAddress))⌝))%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance fp_machineAt0078_unfold : LithiumUnfold (@fp_machineAt0078) := I.
#[export] Typeclasses Opaque fp_machineAt0078.
#[export] Instance fp_machineAt0078_intro `{!islaG Sigma} `{!threadG} (args : KeysToOwnedSliceBlockArgs) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt0078 (args) (returnAddress) (K))
  (fp_machineAt0078_ForwardA0N0 (args) (returnAddress) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

