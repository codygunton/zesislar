Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Definition lookup_hook_code `{!islaG Sigma} `{!threadG}
    (lookup : Z -> option isla_trace) : iProp Sigma :=
  instr_lookup_resources lookup.
Definition lookup_hook_other_code `{!islaG Sigma} `{!threadG}
    (lookup : Z -> option isla_trace) : iProp Sigma :=
  instr_lookup_resources lookup.
Global Instance : LithiumUnfold (@lookup_hook_code) := I.
Global Instance : LithiumUnfold (@lookup_hook_other_code) := I.
Global Typeclasses Opaque lookup_hook_code lookup_hook_other_code.

Set Default Proof Using "Type".

Section disabled.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma lookup_hook_disabled lookup address (Hlookup : is_Some (lookup address)) :
    lookup_hook_code lookup -∗
    find_in_context (FindInstrKind address false) (fun _ => True%I).
  Proof.
    iStartProof. iIntros "Hcode".
    Fail zesu_expose_instruction_lookup.
    iEval (unfold lookup_hook_code) in "Hcode".
    iApply (find_in_context_instr_lookup_resources address false).
    iExists lookup. iSplit; [iAssumption |].
    iSplit; [iPureIntro; exact Hlookup | done].
  Qed.
End disabled.

Section enabled.
  Context `{!islaG Sigma} `{!threadG}.
  Local Instance lookup_hook_enabled : ZesuStepInstructionLookup := I.

  Lemma lookup_hook_reuses_table (trace : isla_trace) first second :
    lookup_hook_code (fun _ => Some trace) -∗
    find_in_context (FindInstrKind first false) (fun _ =>
      find_in_context (FindInstrKind second false) (fun _ => True%I)).
  Proof.
    iStartProof. iIntros "Hcode".
    repeat zesu_liAStep.
  Qed.

  Lemma lookup_hook_other_wrapper (trace : isla_trace) first second :
    lookup_hook_other_code (fun _ => Some trace) -∗
    find_in_context (FindInstrKind first false) (fun _ =>
      find_in_context (FindInstrKind second false) (fun _ => True%I)).
  Proof.
    iStartProof. iIntros "Hcode".
    repeat zesu_liAStep.
  Qed.
End enabled.
