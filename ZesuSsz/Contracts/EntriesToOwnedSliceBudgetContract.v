From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AltFlAllocBudgetPremises.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.ArrayListBudgetContract.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceChargedSelected.
Require ZesuSsz.Stock.Closure.index_sliceAccessList.
Open Scope Z_scope.

(* array_list.Aligned(input.AccessListEntry,null).toOwnedSlice with a step
   bound (plan Stage T, T8). The model of EntriesToOwnedSliceContract.v with
   - the region's code charged (entriesToOwnedSliceChargedCode);
   - the callee premises with their budgets (AltFlAllocBudgetPremises.v);
   - `step_budget entriesToOwnedSliceBudget` owned by the entry
     (ArrayListBudgetContract.v): the longest path of the region's control
     flow graph with the callees' budgets added at their calls
     (`tools/block/budgets.py --function entriesToOwnedSlice`).
   The uncharged contract stays. *)

Notation entriesToOwnedSliceBudget := ((204) : Z) (only parsing).

Definition entriesToOwnedSliceBudgetContractCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (entriesToOwnedSliceChargedCode ∗ altFlAllocatorBudgetPremises ∗
   ziskMemcpyBudgetCallPremise)%I.
Global Instance : LithiumUnfold (@entriesToOwnedSliceBudgetContractCode) := I.
Global Typeclasses Opaque entriesToOwnedSliceBudgetContractCode.

Definition entriesToOwnedSliceBudgetContractModel (returnAddress : Z) :
    IslarisContractModel ToOwnedSliceArgs ToOwnedSliceOutcome :=
  toOwnedSliceBudgetModel (fun Sigma HG HT => @entriesToOwnedSliceBudgetContractCode Sigma HG HT)
    ZesuSsz.Stock.Closure.index_sliceAccessList.sliceAccessList_cfg_step
    entriesElementBytes entriesLog2Alignment entriesEmptyPointer entriesToOwnedSliceBudget
    returnAddress.

(* This declaration states the native proof objective. It does not prove it. *)
Definition EntriesToOwnedSliceBudgetContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect sym_array_list_Aligned_input_AccessListEntry_null_toOwnedSlice
      returnAddress (entriesToOwnedSliceBudgetContractModel returnAddress).
