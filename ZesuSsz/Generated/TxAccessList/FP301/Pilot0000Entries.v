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
Definition fp_machineAt0000_ForwardA0N0_Hist (args : TxAccessListArgs) (returnAddress : Z) : Prop := (∃ (fp_seed_mstatus_bits : bv 64), (((bool_decide ((bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z)) = (BV 64%N 0%Z))) = true) /\ ((((bv_unsigned (bv_and fp_seed_mstatus_bits (BV 64%N 131072%Z))) = (0%Z))%Z)))).

Definition fp_machineAt0000_ForwardA0N0 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) : iProp Sigma := (∃ (x5 : bv 64) (x6 : bv 64) (x7 : bv 64) (x13 : bv 64) (x14 : bv 64) (x15 : bv 64) (x16 : bv 64) (x17 : bv 64) (x28 : bv 64) (x29 : bv 64) (x30 : bv 64) (x31 : bv 64) (frame_old_m104 : bv 64) (frame_old_m96 : bv 64) (frame_old_m88 : bv 64) (frame_old_m80 : bv 64) (frame_old_m72 : bv 64) (frame_old_m64 : bv 64) (frame_old_m56 : bv 64) (frame_old_m48 : bv 64) (frame_old_m40 : bv 64) (frame_old_m32 : bv 64) (frame_old_m24 : bv 64) (frame_old_m16 : bv 64) (frame_old_m8 : bv 64), (reg_col ((txAccessListSysRegs args)) ∗ "x1" ↦ᵣ (RVal_Bits ((txReturnAddress args) : bv 64%N)) ∗ "x2" ↦ᵣ (RVal_Bits ((txStackPointer args) : bv 64%N)) ∗ "x5" ↦ᵣ (RVal_Bits (x5 : bv 64%N)) ∗ "x6" ↦ᵣ (RVal_Bits (x6 : bv 64%N)) ∗ "x7" ↦ᵣ (RVal_Bits (x7 : bv 64%N)) ∗ "x8" ↦ᵣ (RVal_Bits ((txSavedX8 args) : bv 64%N)) ∗ "x9" ↦ᵣ (RVal_Bits ((txSavedX9 args) : bv 64%N)) ∗ "x10" ↦ᵣ (RVal_Bits ((txResultPointer args) : bv 64%N)) ∗ "x11" ↦ᵣ (RVal_Bits ((txAllocatorPointer args) : bv 64%N)) ∗ "x12" ↦ᵣ (RVal_Bits ((txRestPointer args) : bv 64%N)) ∗ "x13" ↦ᵣ (RVal_Bits (x13 : bv 64%N)) ∗ "x14" ↦ᵣ (RVal_Bits (x14 : bv 64%N)) ∗ "x15" ↦ᵣ (RVal_Bits (x15 : bv 64%N)) ∗ "x16" ↦ᵣ (RVal_Bits (x16 : bv 64%N)) ∗ "x17" ↦ᵣ (RVal_Bits (x17 : bv 64%N)) ∗ "x18" ↦ᵣ (RVal_Bits ((txSavedX18 args) : bv 64%N)) ∗ "x19" ↦ᵣ (RVal_Bits ((txSavedX19 args) : bv 64%N)) ∗ "x20" ↦ᵣ (RVal_Bits ((txSavedX20 args) : bv 64%N)) ∗ "x21" ↦ᵣ (RVal_Bits ((txSavedX21 args) : bv 64%N)) ∗ "x22" ↦ᵣ (RVal_Bits ((txSavedX22 args) : bv 64%N)) ∗ "x23" ↦ᵣ (RVal_Bits ((txSavedX23 args) : bv 64%N)) ∗ "x24" ↦ᵣ (RVal_Bits ((txSavedX24 args) : bv 64%N)) ∗ "x25" ↦ᵣ (RVal_Bits ((txSavedX25 args) : bv 64%N)) ∗ "x26" ↦ᵣ (RVal_Bits ((txSavedX26 args) : bv 64%N)) ∗ "x27" ↦ᵣ (RVal_Bits ((txSavedX27 args) : bv 64%N)) ∗ "x28" ↦ᵣ (RVal_Bits (x28 : bv 64%N)) ∗ "x29" ↦ᵣ (RVal_Bits (x29 : bv 64%N)) ∗ "x30" ↦ᵣ (RVal_Bits (x30 : bv 64%N)) ∗ "x31" ↦ᵣ (RVal_Bits (x31 : bv 64%N)) ∗ (bv_unsigned (txInputPointer args)) ↦ₘ∗ (txInputBytes args) ∗ (bv_unsigned (txRestPointer args)) ↦ₘ∗ (txBlockRestBytes args) ∗ (bv_unsigned (txAllocatorPointer args)) ↦ₘ∗ (altFlAllocatorBytes (bv_unsigned (txAllocatorContext args))) ∗ (sym_alt_fl_alloc_vtable) ↦ₘ∗ (altFlVtableBytes) ∗ ZesuSsz.Contracts.AltFlAllocPremises.altFlHeap ∗ (ziskExtraParamsAddress) ↦ₘ∗ (txScratchBefore args) ∗ (bv_unsigned (txResultPointer args)) ↦ₘ? (24) ∗ (((bv_unsigned (txStackPointer args) - 576))%Z) ↦ₘ? (txBlockLocalBytes) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 472%Z))) ↦ₘ (frame_old_m104) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 480%Z))) ↦ₘ (frame_old_m96) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 488%Z))) ↦ₘ (frame_old_m88) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 496%Z))) ↦ₘ (frame_old_m80) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 504%Z))) ↦ₘ (frame_old_m72) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 512%Z))) ↦ₘ (frame_old_m64) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 520%Z))) ↦ₘ (frame_old_m56) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 528%Z))) ↦ₘ (frame_old_m48) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 536%Z))) ↦ₘ (frame_old_m40) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 544%Z))) ↦ₘ (frame_old_m32) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 552%Z))) ↦ₘ (frame_old_m24) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 560%Z))) ↦ₘ (frame_old_m16) ∗ (bv_unsigned (bv_add (bv_add (txStackPointer args) (BV 64%N 18446744073709551040%Z)) (BV 64%N 568%Z))) ↦ₘ (frame_old_m8) ∗ (((bv_unsigned (txStackPointer args) - 576 - 128))%Z) ↦ₘ? (128) ∗ ⌜(txAccessListBlockDomainAt returnAddress args)⌝ ∗ ⌜((bv_unsigned (txReturnAddress args) mod 4 = 0)%Z)⌝ ∗ ⌜zesu_hist (fp_machineAt0000_ForwardA0N0_Hist (args) (returnAddress))⌝))%I.

Definition fp_machineAt0000 `{!islaG Sigma} `{!threadG} (args : TxAccessListArgs) (returnAddress : Z) (K : iProp Sigma) : iProp Sigma := (fp_machineAt0000_ForwardA0N0 (args) (returnAddress) ∗ K)%I.
