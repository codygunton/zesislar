Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A function's folded precondition: a domain predicate whose body is a tree
   of conjunctions, one of which names the return target. *)
Definition jump_domain (R target : Z) : Prop :=
  (0 <= R /\ R < 2 ^ 64) /\ (R mod 4 = 0 /\ R = target).

Section jump_tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* A jump to a symbolic target opens the folded precondition into its
     conjuncts; the conjunct `R = target` substitutes the target. *)
  Lemma folded_jump_symbolic (R target : Z) (ins : option isla_trace) :
    jump_domain R target ->
    instr R ins -∗ find_in_context (FindInstrKind target true) (fun _ => True)%I.
  Proof.
    intros Hdomain. iIntros "Hinstr".
    tryif (match goal with H : (R mod 4 = 0)%Z |- _ => idtac end) then fail else idtac.
    Fail iApply find_in_context_instr_kind_instr; iExists ins; iExact "Hinstr".
    zesu_open_folded_jump_facts.
    match goal with H : (0 <= R)%Z |- _ => idtac end.
    match goal with H : (R < 2 ^ 64)%Z |- _ => idtac end.
    match goal with H : (R mod 4 = 0)%Z |- _ => idtac end.
    tryif (match goal with H : jump_domain _ _ |- _ => idtac end) then fail else idtac.
    iApply find_in_context_instr_kind_instr. iExists ins. iFrame.
  Qed.

  (* A closed requested address leaves the context unchanged. *)
  Lemma folded_jump_closed (R : Z) (ins : option isla_trace) :
    jump_domain R 4096 ->
    instr 4096 ins -∗ find_in_context (FindInstrKind 4096 true) (fun _ => True)%I.
  Proof.
    intros Hdomain. iIntros "Hinstr".
    Fail zesu_open_folded_jump_facts.
    iApply find_in_context_instr_kind_instr. iExists ins. iFrame.
  Qed.

  (* Without a folded precondition the rule makes no progress. *)
  Lemma folded_jump_nothing_folded (R : Z) (ins : option isla_trace) :
    0 <= R -> R mod 4 = 0 ->
    instr R ins -∗ find_in_context (FindInstrKind R true) (fun _ => True)%I.
  Proof.
    intros Hlower Haligned. iIntros "Hinstr".
    Fail zesu_open_folded_jump_facts.
    iApply find_in_context_instr_kind_instr. iExists ins. iFrame.
  Qed.

  (* A goal other than an instruction lookup is refused. *)
  Lemma folded_jump_other_goal (R target : Z) (P : iProp Sigma) :
    jump_domain R target -> P -∗ P.
  Proof.
    intros Hdomain. iIntros "HP".
    Fail zesu_open_folded_jump_facts.
    iExact "HP".
  Qed.
End jump_tests.
