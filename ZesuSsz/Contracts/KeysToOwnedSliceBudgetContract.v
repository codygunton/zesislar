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
Require Import ZesuSsz.Contracts.KeysToOwnedSliceChargedSelected.
Require ZesuSsz.Stock.Closure.index_sliceBytes32.
Open Scope Z_scope.

(* array_list.Aligned([32]u8,null).toOwnedSlice with a step bound (plan
   Stage T, T8). The model of KeysToOwnedSliceContract.v with
   - the region's code charged (keysToOwnedSliceChargedCode);
   - the callee premises with their budgets (AltFlAllocBudgetPremises.v);
   - `step_budget keysToOwnedSliceBudget` owned by the entry
     (ArrayListBudgetContract.v): the longest path of the region's control
     flow graph with the callees' budgets added at their calls
     (`tools/block/budgets.py --function keysToOwnedSlice`).
   The uncharged contract stays. *)

Notation keysToOwnedSliceBudget := ((175) : Z) (only parsing).

Definition keysToOwnedSliceBudgetContractCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (keysToOwnedSliceChargedCode ∗ altFlAllocatorBudgetPremises ∗
   ziskMemcpyBudgetCallPremise)%I.
Global Instance : LithiumUnfold (@keysToOwnedSliceBudgetContractCode) := I.
Global Typeclasses Opaque keysToOwnedSliceBudgetContractCode.

Definition keysToOwnedSliceBudgetContractModel (returnAddress : Z) :
    IslarisContractModel ToOwnedSliceArgs ToOwnedSliceOutcome :=
  toOwnedSliceBudgetModel (fun Sigma HG HT => @keysToOwnedSliceBudgetContractCode Sigma HG HT)
    ZesuSsz.Stock.Closure.index_sliceBytes32.sliceBytes32_cfg_step
    keysElementBytes keysLog2Alignment keysEmptyPointer keysToOwnedSliceBudget returnAddress.

(* This declaration states the native proof objective. It does not prove it. *)
Definition KeysToOwnedSliceBudgetContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect sym_array_list_Aligned_32_u8_null_toOwnedSlice returnAddress
      (keysToOwnedSliceBudgetContractModel returnAddress).
