From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require ZesuSsz.Stock.Closure.index_sliceAccessList.
Open Scope Z_scope.

(* array_list.Aligned(input.AccessListEntry,null).toOwnedSlice: 40-byte elements, alignment 8, empty pointer 8.
   The shared statement is ArrayListContract.v (the toOwnedSlice definitions). *)

(* The selected code is the own map only. The allocator and memcpy entries
   are trusted premises (AltFlAllocPremises.v, ZiskMemcpyPremise.v). *)
Definition entriesToOwnedSliceContractCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (entriesToOwnedSliceSelectedCode ∗ altFlAllocatorPremises ∗ ziskMemcpyCallPremise)%I.
Global Instance : LithiumUnfold (@entriesToOwnedSliceContractCode) := I.
Global Typeclasses Opaque entriesToOwnedSliceContractCode.

Definition entriesToOwnedSliceContractModel (returnAddress : Z) :
    IslarisContractModel ToOwnedSliceArgs ToOwnedSliceOutcome :=
  toOwnedSliceModel (fun Sigma HG HT => @entriesToOwnedSliceContractCode Sigma HG HT)
    ZesuSsz.Stock.Closure.index_sliceAccessList.sliceAccessList_cfg_step
    entriesElementBytes entriesLog2Alignment entriesEmptyPointer returnAddress.

(* This declaration states the native proof objective. It does not prove it. *)
Definition EntriesToOwnedSliceContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect sym_array_list_Aligned_input_AccessListEntry_null_toOwnedSlice returnAddress
      (entriesToOwnedSliceContractModel returnAddress).
