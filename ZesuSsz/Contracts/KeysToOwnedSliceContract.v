From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require ZesuSsz.Stock.Closure.index_sliceBytes32.
Open Scope Z_scope.

(* array_list.Aligned([32]u8,null).toOwnedSlice: 32-byte elements, alignment 1, empty pointer 1.
   The shared statement is ArrayListContract.v (the toOwnedSlice definitions). *)

(* The selected code is the own map only. The allocator and memcpy entries
   are trusted premises (AltFlAllocPremises.v, ZiskMemcpyPremise.v). *)
Definition keysToOwnedSliceContractCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (keysToOwnedSliceSelectedCode ∗ altFlAllocatorPremises ∗ ziskMemcpyCallPremise)%I.
Global Instance : LithiumUnfold (@keysToOwnedSliceContractCode) := I.
Global Typeclasses Opaque keysToOwnedSliceContractCode.

Definition keysToOwnedSliceContractModel (returnAddress : Z) :
    IslarisContractModel ToOwnedSliceArgs ToOwnedSliceOutcome :=
  toOwnedSliceModel (fun Sigma HG HT => @keysToOwnedSliceContractCode Sigma HG HT)
    ZesuSsz.Stock.Closure.index_sliceBytes32.sliceBytes32_cfg_step
    keysElementBytes keysLog2Alignment keysEmptyPointer returnAddress.

(* This declaration states the native proof objective. It does not prove it. *)
Definition KeysToOwnedSliceContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect sym_array_list_Aligned_32_u8_null_toOwnedSlice returnAddress
      (keysToOwnedSliceContractModel returnAddress).
