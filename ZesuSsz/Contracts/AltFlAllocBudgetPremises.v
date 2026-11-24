Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Automation2.StepBudget.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Open Scope Z_scope.

(* Step budgets of the allocator and memcpy entries (plan Stage T, T6).
   Each premise is the existing one (AltFlAllocPremises.v,
   ZiskMemcpyPremise.v) with `step_budget K` added to the precondition the
   caller hands over: started at the callee's entry with K step credits, the
   callee runs to its return under its call specification. K is the number of
   instructions on the longest path of the callee from its entry to its
   return (`tools/block/budgets.py --function <callee>` over
   build/stock-zisk/cfg.json; none of the four has a loop or a call). One
   credit is one fetch of a charged instruction; the entry's budget pays for
   its own first instruction, and the fetch at the caller's return address
   is the caller's.

   Two readings, and only one is a trust item.
   - Derived (`*_from_existing_premise_uncounted` below): each premise
     follows from the existing one by dropping the budget. Used that way the
     callee's code is uncharged: its instructions are NOT counted by the
     bound, which is then relative (it counts the caller's charged
     instructions only).
   - Assumed: the bound counts the allocator's and memcpy's instructions
     only in a run whose charged set holds their code and where these
     premises are assumed. That assumption is the trust item: the callee
     returns within K fetches, K its loop-free longest path in cfg.json.
   The existing premises are unchanged. *)

Notation altFlAllocStepBudget := ((53) : Z) (only parsing).
Notation altFlRemapStepBudget := ((9) : Z) (only parsing).
Notation altFlFreeStepBudget := ((42) : Z) (only parsing).
Notation ziskMemcpyStepBudget := ((3) : Z) (only parsing).

Definition altFlAllocBudgetCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_alt_fl_alloc_alloc
     (step_budget altFlAllocStepBudget ∗ altFlAllocCallSpec))%I.
Global Instance : LithiumUnfold (@altFlAllocBudgetCallPremise) := I.
Global Typeclasses Opaque altFlAllocBudgetCallPremise.

Definition altFlRemapBudgetCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_alt_fl_alloc_remap
     (step_budget altFlRemapStepBudget ∗ altFlRemapCallSpec))%I.
Global Instance : LithiumUnfold (@altFlRemapBudgetCallPremise) := I.
Global Typeclasses Opaque altFlRemapBudgetCallPremise.

Definition altFlFreeBudgetCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_alt_fl_alloc_free
     (step_budget altFlFreeStepBudget ∗ altFlFreeCallSpec))%I.
Global Instance : LithiumUnfold (@altFlFreeBudgetCallPremise) := I.
Global Typeclasses Opaque altFlFreeBudgetCallPremise.

Definition altFlAllocatorBudgetPremises `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (altFlAllocBudgetCallPremise ∗ altFlRemapBudgetCallPremise ∗
   altFlFreeBudgetCallPremise)%I.
Global Instance : LithiumUnfold (@altFlAllocatorBudgetPremises) := I.
Global Typeclasses Opaque altFlAllocatorBudgetPremises.

Definition ziskMemcpyBudgetCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_memcpy (step_budget ziskMemcpyStepBudget ∗ ziskMemcpyCallSpec))%I.
Global Instance : LithiumUnfold (@ziskMemcpyBudgetCallPremise) := I.
Global Typeclasses Opaque ziskMemcpyBudgetCallPremise.

Section from_existing_premise.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma instr_pre_budget_dropped (a K : Z) (P : iProp Sigma) :
    instr_pre a P ⊢ instr_pre a (step_budget K ∗ P).
  Proof.
    iIntros "H". iApply (instr_pre_wand with "H"); [done|done|].
    iIntros "[_ $]".
  Qed.

  Lemma altFlAllocBudgetCallPremise_from_existing_premise_uncounted :
    altFlAllocCallPremise ⊢ altFlAllocBudgetCallPremise.
  Proof.
    rewrite /altFlAllocCallPremise /altFlAllocBudgetCallPremise.
    iIntros "#H !>". by iApply instr_pre_budget_dropped.
  Qed.

  Lemma altFlRemapBudgetCallPremise_from_existing_premise_uncounted :
    altFlRemapCallPremise ⊢ altFlRemapBudgetCallPremise.
  Proof.
    rewrite /altFlRemapCallPremise /altFlRemapBudgetCallPremise.
    iIntros "#H !>". by iApply instr_pre_budget_dropped.
  Qed.

  Lemma altFlFreeBudgetCallPremise_from_existing_premise_uncounted :
    altFlFreeCallPremise ⊢ altFlFreeBudgetCallPremise.
  Proof.
    rewrite /altFlFreeCallPremise /altFlFreeBudgetCallPremise.
    iIntros "#H !>". by iApply instr_pre_budget_dropped.
  Qed.

  Lemma ziskMemcpyBudgetCallPremise_from_existing_premise_uncounted :
    ziskMemcpyCallPremise ⊢ ziskMemcpyBudgetCallPremise.
  Proof.
    rewrite /ziskMemcpyCallPremise /ziskMemcpyBudgetCallPremise.
    iIntros "#H !>". by iApply instr_pre_budget_dropped.
  Qed.
End from_existing_premise.
