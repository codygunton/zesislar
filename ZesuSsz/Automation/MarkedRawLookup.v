(* Select the raw trace at a marked address. The marker is supplied by a
   segment, so other addresses continue to use their table entries. *)

Require Import ZesuSsz.Automation.All.
Require Import InstrSpecs.Lookup.
Require Import isla.riscv64.riscv64.

Class ZesuRawTraceAt (lookup : Z -> option isla_trace) (address : Z) : Prop :=
  zesu_raw_trace_at : is_Some (lookup address).

Section marked_raw_lookup.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma find_in_context_zesu_marked_raw address lookup
      `{!ZesuRawTraceAt lookup address} later continuation :
    (instr_lookup_resources lookup ∗ continuation (IKInstr (lookup address)))
    ⊢ find_in_context (FindInstrKind address later) continuation.
  Proof.
    iDestruct 1 as "(Hcode & Hcontinuation)".
    iExists (IKInstr (lookup address)) => /=. iFrame "Hcontinuation".
    rewrite /instr_lookup_resources.
    iApply ("Hcode" $! address).
    iPureIntro.
    match goal with
    | H : ZesuRawTraceAt lookup address |- _ => exact H
    end.
  Qed.

  Definition find_in_context_zesu_marked_raw_inst address :=
    [instance find_in_context_zesu_marked_raw address with FICSyntactic].
  Global Existing Instance find_in_context_zesu_marked_raw_inst | 7.
End marked_raw_lookup.
