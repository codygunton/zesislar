From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.

(** Lazy access to charged instruction resources: every fetch of an address
    in this table consumes one [step_credits 1]. The form mirrors
    [instr_lookup_resources] of [InstrSpecs/Lookup.v]. *)

Definition instr_lookup_resources_charged `{!islaG Sigma} `{!threadG}
    (lookup : Z -> option isla_trace) : iProp Sigma :=
  (□ ∀ address trace, ⌜lookup address = Some trace⌝ -∗
    instr_charged address trace)%I.

Global Instance instr_lookup_resources_charged_persistent
    `{!islaG Sigma} `{!threadG} (lookup : Z -> option isla_trace) :
    Persistent (instr_lookup_resources_charged lookup) := _.

Global Typeclasses Opaque instr_lookup_resources_charged.

Global Instance instr_lookup_resources_charged_intro_persistent
    `{!islaG Sigma} `{!threadG} (lookup : Z -> option isla_trace) :
    IntroPersistent (instr_lookup_resources_charged lookup)
      (instr_lookup_resources_charged lookup).
Proof. constructor. iIntros "#$". Qed.

(** The trace that a charged table holds at one address, as a Lithium tactic
    goal ([li_tactic]). Its [LiTactic] instance
    (`ZesuSsz/Automation2/StepBudget.v`) evaluates the lookup at a closed
    address only. *)
Definition charged_trace_at {Sigma : gFunctors}
    (lookup : Z -> option isla_trace) (address : Z)
    (T : isla_trace -> iProp Sigma) : iProp Sigma :=
  (∃ trace, ⌜lookup address = Some trace⌝ ∗ T trace)%I.
Arguments charged_trace_at : simpl never.
Global Typeclasses Opaque charged_trace_at.

Set Default Proof Using "Type".

Section automation.
  Context `{!islaG Sigma} `{!threadG}.

  (** The charged table answers a fetch with [IKCharged] and the trace that
      the lookup holds at [address]. *)
  Lemma find_in_context_instr_lookup_resources_charged address later continuation :
    (∃ lookup,
      instr_lookup_resources_charged lookup ∗
      li_tactic (charged_trace_at lookup address)
        (fun trace => continuation (IKCharged trace)))
    ⊢ find_in_context (FindInstrKind address later) continuation.
  Proof.
    iDestruct 1 as (lookup) "(#Hcode & Hcontinuation)".
    rewrite /li_tactic /charged_trace_at.
    iDestruct "Hcontinuation" as (trace Hlookup) "Hcontinuation".
    iExists (IKCharged trace) => /=. iFrame "Hcontinuation".
    rewrite /instr_lookup_resources_charged.
    iApply ("Hcode" $! address trace). iPureIntro. exact Hlookup.
  Qed.

  Definition find_in_context_instr_lookup_resources_charged_inst address :=
    [instance find_in_context_instr_lookup_resources_charged address with FICSyntactic].
  Global Existing Instance find_in_context_instr_lookup_resources_charged_inst | 12.

  (** The same answer when the trace at [address] is already known. *)
  Lemma find_in_context_instr_lookup_resources_charged_at
      address lookup trace (Hlookup : lookup address = Some trace)
      later continuation :
    (instr_lookup_resources_charged lookup ∗
      continuation (IKCharged trace))
    ⊢ find_in_context (FindInstrKind address later) continuation.
  Proof.
    iDestruct 1 as "(#Hcode & Hcontinuation)".
    iExists (IKCharged trace) => /=. iFrame "Hcontinuation".
    rewrite /instr_lookup_resources_charged.
    iApply ("Hcode" $! address trace). iPureIntro. exact Hlookup.
  Qed.

End automation.
