(* Generated from FP-20261102-Level1-domain-v1. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Export ZesuSsz.Interfaces.DecodeItem.
Require Export ZesuSsz.Interfaces.KeysToOwnedSlice.
Require Export ZesuSsz.Interfaces.EntriesToOwnedSlice.
Require Export ZesuSsz.Interfaces.KeysEnsureCapacity.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Require Export ZesuSsz.Compliance.TxAccessListHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import ZesuSsz.Automation2.Hist.
Require Import ZesuSsz.Generated.TxAccessList.FP301.Pilot0068Entries.
#[export] Typeclasses Opaque fp_machineAt0068_ForwardA0N0_Hist.
#[export] Instance fp_machineAt0068_ForwardA0N0_unfold : LithiumUnfold (@fp_machineAt0068_ForwardA0N0) := I.
#[export] Typeclasses Opaque fp_machineAt0068_ForwardA0N0.
#[export] Instance fp_machineAt0068_ForwardA0N0_intro `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt0068_ForwardA0N0 (args) (returnAddress))
  (∃ (call_x1 : bv 64) (call_x5 : bv 64) (call_x6 : bv 64) (call_x7 : bv 64) (call_x10 : bv 64) (call_x11 : bv 64) (call_x12 : bv 64) (call_x13 : bv 64) (call_x14 : bv 64) (call_x15 : bv 64) (call_x16 : bv 64) (call_x17 : bv 64) (call_x28 : bv 64) (call_x29 : bv 64) (call_x30 : bv 64) (call_x31 : bv 64) (call_after : DecodeItemOutcome), (reg_col ((txAccessListSysRegs args)) ∗ "x1" ↦ᵣ (RVal_Bits (call_x1 : bv 64%N)) ∗ "x2" ↦ᵣ (RVal_Bits ((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) : bv 64%N)) ∗ "x5" ↦ᵣ (RVal_Bits (call_x5 : bv 64%N)) ∗ "x6" ↦ᵣ (RVal_Bits (call_x6 : bv 64%N)) ∗ "x7" ↦ᵣ (RVal_Bits (call_x7 : bv 64%N)) ∗ "x8" ↦ᵣ (RVal_Bits ((bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) : bv 64%N)) ∗ "x9" ↦ᵣ (RVal_Bits ((txResultPointer args) : bv 64%N)) ∗ "x10" ↦ᵣ (RVal_Bits (call_x10 : bv 64%N)) ∗ "x11" ↦ᵣ (RVal_Bits (call_x11 : bv 64%N)) ∗ "x12" ↦ᵣ (RVal_Bits (call_x12 : bv 64%N)) ∗ "x13" ↦ᵣ (RVal_Bits (call_x13 : bv 64%N)) ∗ "x14" ↦ᵣ (RVal_Bits (call_x14 : bv 64%N)) ∗ "x15" ↦ᵣ (RVal_Bits (call_x15 : bv 64%N)) ∗ "x16" ↦ᵣ (RVal_Bits (call_x16 : bv 64%N)) ∗ "x17" ↦ᵣ (RVal_Bits (call_x17 : bv 64%N)) ∗ "x18" ↦ᵣ (RVal_Bits ((txAllocatorPointer args) : bv 64%N)) ∗ "x19" ↦ᵣ (RVal_Bits ((txReturnAddress args) : bv 64%N)) ∗ "x20" ↦ᵣ (RVal_Bits ((txSavedX20 args) : bv 64%N)) ∗ "x21" ↦ᵣ (RVal_Bits ((txSavedX21 args) : bv 64%N)) ∗ "x22" ↦ᵣ (RVal_Bits ((txRestPointer args) : bv 64%N)) ∗ "x23" ↦ᵣ (RVal_Bits ((txInputPointer args) : bv 64%N)) ∗ "x24" ↦ᵣ (RVal_Bits ((txInputLength args) : bv 64%N)) ∗ "x25" ↦ᵣ (RVal_Bits ((txSavedX25 args) : bv 64%N)) ∗ "x26" ↦ᵣ (RVal_Bits ((txSavedX26 args) : bv 64%N)) ∗ "x27" ↦ᵣ (RVal_Bits ((txSavedX27 args) : bv 64%N)) ∗ "x28" ↦ᵣ (RVal_Bits (call_x28 : bv 64%N)) ∗ "x29" ↦ᵣ (RVal_Bits (call_x29 : bv 64%N)) ∗ "x30" ↦ᵣ (RVal_Bits (call_x30 : bv 64%N)) ∗ "x31" ↦ᵣ (RVal_Bits (call_x31 : bv 64%N)) ∗ (bv_unsigned (txInputPointer args)) ↦ₘ∗ (txInputBytes args) ∗ (bv_unsigned (txRestPointer args)) ↦ₘ∗ (txBlockRestBytes args) ∗ (bv_unsigned (txAllocatorPointer args)) ↦ₘ∗ (altFlAllocatorBytes (bv_unsigned (txAllocatorContext args))) ∗ (sym_alt_fl_alloc_vtable) ↦ₘ∗ (altFlVtableBytes) ∗ ZesuSsz.Contracts.AltFlAllocPremises.altFlHeap ∗ (ziskExtraParamsAddress) ↦ₘ∗ (txScratchBefore args) ∗ (bv_unsigned (txResultPointer args)) ↦ₘ? (24) ∗ (((bv_unsigned (txStackPointer args) - 576))%Z) ↦ₘ? (88) ∗ ((((bv_unsigned (txStackPointer args) - 576) + 88))%Z) ↦ₘ∗ (call_after) ∗ ((((bv_unsigned (txStackPointer args) - 576) + 128))%Z) ↦ₘ? (344) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 472%Z))) ↦ₘ (txSavedX27 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 480%Z))) ↦ₘ (txSavedX26 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 488%Z))) ↦ₘ (txSavedX25 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 496%Z))) ↦ₘ (txSavedX24 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 504%Z))) ↦ₘ (txSavedX23 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 512%Z))) ↦ₘ (txSavedX22 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 520%Z))) ↦ₘ (txSavedX21 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 528%Z))) ↦ₘ (txSavedX20 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 536%Z))) ↦ₘ (txSavedX19 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 544%Z))) ↦ₘ (txSavedX18 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 552%Z))) ↦ₘ (txSavedX9 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 560%Z))) ↦ₘ (txSavedX8 args) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 568%Z))) ↦ₘ (txReturnAddress args) ∗ (((bv_unsigned (txStackPointer args) - 576 - 128))%Z) ↦ₘ? (128) ∗ ⌜(txAccessListBlockDomainAt returnAddress args)⌝ ∗ ⌜((bv_unsigned (txReturnAddress args) mod 4 = 0)%Z)⌝ ∗ ⌜((List.length call_after = 40)%nat)⌝ ∗ ⌜(∃ (call_arg_x13 : bv 64) (call_arg_x14 : bv 64) (call_arg_x15 : bv 64) (call_arg_x16 : bv 64) (call_arg_x17 : bv 64) (call_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 576%Z)) (BV 64%N 18446744073709551128%Z))); ((txInputPointer args)); ((txInputLength args)); (call_arg_x13); (call_arg_x14); (call_arg_x15); (call_arg_x16); (call_arg_x17)]) (((bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)))) (bv_unsigned (((txInputEnd args)))) (txInputBytes args) call_before) (call_after)))⌝ ∗ ⌜zesu_hist (fp_machineAt0068_ForwardA0N0_Hist (args) (returnAddress))⌝))%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance fp_machineAt0068_unfold : LithiumUnfold (@fp_machineAt0068) := I.
#[export] Typeclasses Opaque fp_machineAt0068.
#[export] Instance fp_machineAt0068_intro `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt0068 (args) (returnAddress) (K))
  (fp_machineAt0068_ForwardA0N0 (args) (returnAddress) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

