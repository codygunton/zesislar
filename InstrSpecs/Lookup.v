From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.

(** Lazy access to generated instruction resources. *)

Definition instr_lookup_resources `{!islaG Sigma} `{!threadG}
    (lookup : Z -> option isla_trace) : iProp Sigma :=
  (□ ∀ address, ⌜is_Some (lookup address)⌝ -∗
    instr address (lookup address))%I.

Global Instance instr_lookup_resources_persistent `{!islaG Sigma} `{!threadG}
    (lookup : Z -> option isla_trace) :
    Persistent (instr_lookup_resources lookup) := _.

Global Typeclasses Opaque instr_lookup_resources.

Definition instr_body_lookup_resources `{!islaG Sigma} `{!threadG}
    (lookup : Z -> option (iProp Sigma)) : iProp Sigma :=
  (□ ∀ address body, ⌜lookup address = Some body⌝ -∗
    instr_body address body)%I.

Global Instance instr_body_lookup_resources_persistent
    `{!islaG Sigma} `{!threadG} (lookup : Z -> option (iProp Sigma)) :
    Persistent (instr_body_lookup_resources lookup) := _.

Global Typeclasses Opaque instr_body_lookup_resources.

Global Instance instr_body_lookup_resources_intro_persistent
    `{!islaG Sigma} `{!threadG} (lookup : Z -> option (iProp Sigma)) :
    IntroPersistent (instr_body_lookup_resources lookup)
      (instr_body_lookup_resources lookup).
Proof. constructor. iIntros "#$". Qed.

Global Instance instr_lookup_resources_intro_persistent
    `{!islaG Sigma} `{!threadG} (lookup : Z -> option isla_trace) :
    IntroPersistent (instr_lookup_resources lookup)
      (instr_lookup_resources lookup).
Proof. constructor. iIntros "#$". Qed.

Section automation.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma find_in_context_instr_lookup_resources address later continuation :
    (∃ lookup,
      instr_lookup_resources lookup ∗
      ⌜is_Some (lookup address)⌝ ∗
      continuation (IKInstr (lookup address)))
    ⊢ find_in_context (FindInstrKind address later) continuation.
  Proof.
    iDestruct 1 as (lookup) "(Hcode & %Hlookup & Hcontinuation)".
    iExists (IKInstr (lookup address)) => /=. iFrame "Hcontinuation".
    rewrite /instr_lookup_resources.
    iApply ("Hcode" $! address). iPureIntro. exact Hlookup.
  Qed.

  Definition find_in_context_instr_lookup_resources_inst address :=
    [instance find_in_context_instr_lookup_resources address with FICSyntactic].
  Global Existing Instance find_in_context_instr_lookup_resources_inst | 11.

  Lemma find_in_context_instr_body_lookup_resources address later continuation :
    (∃ lookup body,
      instr_body_lookup_resources lookup ∗
      ⌜lookup address = Some body⌝ ∗
      continuation (IKPre false body))
    ⊢ find_in_context (FindInstrKind address later) continuation.
  Proof.
    iDestruct 1 as (lookup body) "(Hcode & %Hlookup & Hcontinuation)".
    iExists (IKPre false body) => /=. iFrame "Hcontinuation".
    rewrite /instr_body_lookup_resources.
    iApply ("Hcode" $! address body). iPureIntro. exact Hlookup.
  Qed.

  Definition find_in_context_instr_body_lookup_resources_inst address :=
    [instance find_in_context_instr_body_lookup_resources address with FICSyntactic].

  Lemma find_in_context_instr_body_lookup_resources_at
      address lookup body (Hlookup : lookup address = Some body)
      later continuation :
    (instr_body_lookup_resources lookup ∗
      continuation (IKPre false body))
    ⊢ find_in_context (FindInstrKind address later) continuation.
  Proof.
    iDestruct 1 as "(Hcode & Hcontinuation)".
    iExists (IKPre false body) => /=. iFrame "Hcontinuation".
    rewrite /instr_body_lookup_resources.
    iApply ("Hcode" $! address body). iPureIntro. exact Hlookup.
  Qed.

End automation.
