Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Guard of zesu_open_folded_jump_facts: it opens a folded precondition for a
   symbolic jump target only when no owned `instr_pre` at that address answers
   the lookup. *)
Definition guard_jump_domain (R target : Z) : Prop :=
  (0 <= R /\ R < 2 ^ 64) /\ (R mod 4 = 0 /\ R = target).

Section jump_guard_tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* Fires: only an instruction at R is owned; the target is identified with
     R through the folded precondition. *)
  Lemma folded_jump_guard_fires (R target : Z) (ins : option isla_trace) :
    guard_jump_domain R target ->
    instr R ins -∗ find_in_context (FindInstrKind target true) (fun _ => True)%I.
  Proof.
    intros Hdomain. iIntros "Hinstr".
    zesu_open_folded_jump_facts.
    tryif (match goal with H : guard_jump_domain _ _ |- _ => idtac end) then fail else idtac.
    iApply find_in_context_instr_kind_instr. iExists ins. iFrame.
  Qed.

  (* Skipped: an `instr_pre` at the requested address is owned; the folded
     precondition stays folded and the owned precondition answers. *)
  Lemma folded_jump_guard_skips_owned_pre (R target : Z) (P : iProp Sigma) :
    guard_jump_domain R target ->
    instr_pre target P -∗ find_in_context (FindInstrKind target true) (fun _ => True)%I.
  Proof.
    intros Hdomain. iIntros "Hpre".
    Fail zesu_open_folded_jump_facts.
    match goal with H : guard_jump_domain R target |- _ => idtac end.
    zesu_prefer_owned_instr_pre.
  Qed.
End jump_guard_tests.
