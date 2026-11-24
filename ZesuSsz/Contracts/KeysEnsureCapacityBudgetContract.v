From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AltFlAllocBudgetPremises.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityChargedSelected.
Require ZesuSsz.Stock.Closure.index_ensureTotalCapacity.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* keysEnsureCapacity with a step bound (plan Stage T, T6). The model of
   KeysEnsureCapacityContract.v, unchanged in its arguments, outcome
   relation, entry and exit resources, with
   - the region's code charged (keysEnsureCapacityChargedCode): each fetch
     of one of its instructions consumes one step credit;
   - the callee premises with their budgets (AltFlAllocBudgetPremises.v);
   - `step_budget keysEnsureCapacityBudget` owned by the entry: the number
     of instruction fetches from the entry to the return, the entry's own
     instruction included. It is the longest path of the region's control
     flow graph with the callees' budgets added at their calls
     (`tools/block/budgets.py --function keysEnsureCapacity`, over
     build/stock-zisk/cfg.json and the profile's unreachable blocks).
   The fetch at the return address belongs to the caller. *)

Notation keysEnsureCapacityBudget := ((197) : Z) (only parsing).

Definition keysEnsureCapacityBudgetContractCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (keysEnsureCapacityChargedCode ∗ altFlAllocatorBudgetPremises ∗
   ziskMemcpyBudgetCallPremise)%I.
Global Instance : LithiumUnfold (@keysEnsureCapacityBudgetContractCode) := I.
Global Typeclasses Opaque keysEnsureCapacityBudgetContractCode.

Definition keysEnsureCapacityBudgetResources `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) :
    IslarisContractResources EnsureCapacityArgs EnsureCapacityOutcome :=
  {| islarisCode := keysEnsureCapacityBudgetContractCode;
     islarisEntry := fun args =>
       (⌜bv_unsigned (ensureReturnAddress args) = returnAddress⌝ ∗
        keysEnsureCapacityEntry args ∗
        step_budget keysEnsureCapacityBudget)%I;
     islarisExit := keysEnsureCapacityExit |}.

Definition keysEnsureCapacityBudgetContractModel (returnAddress : Z) :
    IslarisContractModel EnsureCapacityArgs EnsureCapacityOutcome :=
  {| islarisContractAllows := fun args outcome =>
       bv_unsigned (ensureReturnAddress args) = returnAddress /\
       keysEnsureCapacityDomain args /\
       keysEnsureCapacityAllows args outcome;
     islarisContractStep :=
       ZesuSsz.Stock.Closure.index_ensureTotalCapacity.ensureTotalCapacity_cfg_step;
     islarisContractResources := fun Sigma HG HT =>
       @keysEnsureCapacityBudgetResources Sigma HG HT returnAddress |}.

(* This declaration states the native proof objective. It does not prove it. *)
Definition KeysEnsureCapacityBudgetContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect sym_array_list_Aligned_32_u8_null_ensureTotalCapacity
      returnAddress (keysEnsureCapacityBudgetContractModel returnAddress).
