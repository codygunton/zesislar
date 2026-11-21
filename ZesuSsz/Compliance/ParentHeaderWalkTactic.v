(* Step 2.4 M1, amendment 14: the one proof of decodeParentHeader's walk
   obligations. Owner: compliance proof (hand-written, once). The generator
   declares, per edge from a field call's block into its return site,
   `fp_edge<src>_<ret>_Walk` (Generated/DecodeParentHeader/FP301/
   EdgeObligations.v): from the call block's history (the walk fact of the
   previous return site and the guards the code took since), its visible
   facts (domain, named equations, the newest call's record and guards),
   the walk fact of this call's window (`ParentHeaderWalkFact.v`).
   `ph_edge_walk` proves every such declaration: open the history, read the
   guards as unsigned facts, replace each named register by its definition,
   then apply the step lemma of the edge's kind (the outer item: start; a
   skipped field: skip) and close its premises from the context. Pure
   lemmas and pure tactics only. *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions bitvector.tactics.
Require Import ZesuSsz.Contracts.NamedEquation.
Require Import ZesuSsz.Contracts.ParentHeaderWalkFact.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Compliance.ParentHeaderCandidateFacts.
Require Import ZesuSsz.Compliance.ParentHeaderEdgeTactic.

(* A named register is replaced by its definition everywhere. *)
Ltac ph_walk_names :=
  repeat match goal with
  | H : zesu_named_eq ?x _ |- _ => is_var x; destruct H as [H]; subst x
  end.

(* The walk facts of the history, as the step lemmas take them. *)
Ltac ph_walk_unfold :=
  repeat match goal with
  | H : parentHeaderWalkStart _ _ |- _ => unfold parentHeaderWalkStart in H
  | H : parentHeaderWalkSkipped _ _ _ _ _ _ |- _ => unfold parentHeaderWalkSkipped in H
  | H : parentHeaderWalkSkippedState _ _ _ _ _ _ |- _ => unfold parentHeaderWalkSkippedState in H
  end.

Ltac ph_edge_walk :=
  ph_edge_intro; ph_edge_open; ph_walk_names; ph_walk_unfold;
  first
    [ eapply parentHeaderWalkStartOf;
        [ eapply parentHeaderWellFormedFits; eassumption
        | eapply parentHeaderCallC1B; eassumption
        | eassumption | eassumption | eassumption ]
    | eapply parentHeaderWalkSkipOf;
        [ reflexivity | reflexivity | eassumption
        | eapply parentHeaderCallC1B; eassumption | eassumption | eassumption ]
    | eapply parentHeaderWalkSkipStateOf;
        [ reflexivity | reflexivity | eassumption
        | eapply parentHeaderCallC1B; eassumption | eassumption ]
    | eapply parentHeaderWalkIntegerOf;
        [ reflexivity | reflexivity | eassumption
        | eapply parentHeaderCallC1B; eassumption
        | eassumption | eassumption | eassumption | eassumption | reflexivity ]
    | eapply parentHeaderWalkIntegerLeftOf;
        [ reflexivity | reflexivity | eassumption
        | eapply parentHeaderCallC1B; eassumption
        | eassumption | eassumption | eassumption | eassumption | eassumption | reflexivity ]
    (* A success join (0x03bc): nothing left before an optional field. The
       walk fact the step starts from is chosen by backtracking. *)
    | match goal with
      | H : parentHeaderWalkState _ _ _ _ _ |- candidateParentHeader _ = candidateHeaderSuccess _ =>
          refine (parentHeaderSuccessAfterInteger _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _);
          first [ reflexivity | eapply parentHeaderCallC1B; eassumption | eassumption ]
      | H : parentHeaderWalkAt _ _ _ _ _ |- candidateParentHeader _ = candidateHeaderSuccess _ =>
          refine (parentHeaderSuccessAfterSkip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _);
          first [ reflexivity | eapply parentHeaderCallC1B; eassumption | eassumption ]
      end ].
