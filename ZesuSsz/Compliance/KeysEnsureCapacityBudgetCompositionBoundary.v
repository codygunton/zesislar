(* The boundary terms of the charged keysEnsureCapacity block composition
   (plan Stage T, T6). The postcondition and the continuation are those of
   the uncharged composition (KeysEnsureCapacityCompositionBoundary.v): the
   contract exit is unchanged. KeysEnsureCapacityBudgetBlockObligations.v
   (generated) and KeysEnsureCapacityBudgetGeneratedComposition.v use them. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.AltFlAllocBudgetPremises.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityChargedSelected.
Require Export ZesuSsz.Compliance.KeysEnsureCapacityCompositionBoundary.
Local Open Scope Z_scope.

(* The table code: the charged own code and the budgeted callee premises of
   the contract. *)
Definition keysEnsureCapacityBudgetTableCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (keysEnsureCapacityChargedCode ∗
   □ instr_pre sym_alt_fl_alloc_alloc (step_budget altFlAllocStepBudget ∗ altFlAllocCallSpec) ∗
   □ instr_pre sym_alt_fl_alloc_remap (step_budget altFlRemapStepBudget ∗ altFlRemapCallSpec) ∗
   □ instr_pre sym_alt_fl_alloc_free (step_budget altFlFreeStepBudget ∗ altFlFreeCallSpec) ∗
   □ instr_pre sym_memcpy (step_budget ziskMemcpyStepBudget ∗ ziskMemcpyCallSpec))%I.
Global Instance : LithiumUnfold (@keysEnsureCapacityBudgetTableCode) := I.
Global Typeclasses Opaque keysEnsureCapacityBudgetTableCode.

(* A block statement tagged with its block address and its entry constant. *)
Definition keysEnsureCapacityBudgetBlockAt (address : Z) {A : Type} (entry : A) (statement : Prop) : Prop :=
  statement.
