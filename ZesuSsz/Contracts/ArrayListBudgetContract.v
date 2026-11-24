From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Contracts.ArrayListContract.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* toOwnedSlice with a step bound (plan Stage T, T8). The model of
   ArrayListContract.v (toOwnedSliceModel), unchanged in its arguments,
   outcome relation, entry and exit resources, with `step_budget budget`
   owned by the entry: the number of instruction fetches from the entry to
   the return, the entry's own instruction included. The code (charged own
   code and budgeted callee premises) and the budget are the instance's. The
   fetch at the return address belongs to the caller. *)

Definition toOwnedSliceBudgetResources `{!islaG Sigma} `{!threadG}
    (code : iProp Sigma) (elementBytes log2Align budget returnAddress : Z) :
    IslarisContractResources ToOwnedSliceArgs ToOwnedSliceOutcome :=
  {| islarisCode := code;
     islarisEntry := fun args =>
       (⌜bv_unsigned (toOwnedReturnAddress args) = returnAddress⌝ ∗
        toOwnedSliceEntry elementBytes log2Align args ∗
        step_budget budget)%I;
     islarisExit := toOwnedSliceExit elementBytes log2Align |}.

Definition toOwnedSliceBudgetModel
    (code : forall (Sigma : gFunctors), islaG Sigma -> threadG -> iProp Sigma)
    (step : Z -> Z -> Prop)
    (elementBytes log2Align emptyPointer budget returnAddress : Z) :
    IslarisContractModel ToOwnedSliceArgs ToOwnedSliceOutcome :=
  {| islarisContractAllows := fun args outcome =>
       bv_unsigned (toOwnedReturnAddress args) = returnAddress /\
       toOwnedSliceDomain elementBytes args /\
       toOwnedSliceAllows elementBytes emptyPointer args outcome;
     islarisContractStep := step;
     islarisContractResources := fun Sigma HG HT =>
       @toOwnedSliceBudgetResources Sigma HG HT (code Sigma HG HT)
         elementBytes log2Align budget returnAddress |}.
