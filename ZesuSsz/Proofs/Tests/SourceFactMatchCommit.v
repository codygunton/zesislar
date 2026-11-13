From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Source fact matching commits to the first solution of a segment of
   requested facts whose open evars no later fact and no other part of the
   goal shares; inside a segment it keeps backtracking. Each pair below
   ([ai < 10] then [0 <= ai]) is one segment with two candidates, and the
   fixed fact [bound < 0] sits between 10 pairs on each side. Without the
   commit, its refusal retries every candidate combination of the pairs
   matched before it (2^10). *)

Definition source_match_commit_pairs (bound : Z) : Prop :=
  exists a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20,
    a1 < 10 /\ 0 <= a1 /\ a2 < 10 /\ 0 <= a2 /\ a3 < 10 /\ 0 <= a3 /\ a4 < 10 /\ 0 <= a4 /\ a5 < 10 /\ 0 <= a5 /\ a6 < 10 /\ 0 <= a6 /\ a7 < 10 /\ 0 <= a7 /\ a8 < 10 /\ 0 <= a8 /\ a9 < 10 /\ 0 <= a9 /\ a10 < 10 /\ 0 <= a10 /\
    bound < 0 /\
    a11 < 10 /\ 0 <= a11 /\ a12 < 10 /\ 0 <= a12 /\ a13 < 10 /\ 0 <= a13 /\ a14 < 10 /\ 0 <= a14 /\ a15 < 10 /\ 0 <= a15 /\ a16 < 10 /\ 0 <= a16 /\ a17 < 10 /\ 0 <= a17 /\ a18 < 10 /\ 0 <= a18 /\ a19 < 10 /\ 0 <= a19 /\ a20 < 10 /\ 0 <= a20.

Ltac source_match_commit_goal :=
  lazymatch goal with
  | |- ?requested => ZesuSsz.Automation2.SourceFactMatching.zesu_source_match_fact requested ltac:(idtac)
  end.

Lemma source_match_commit_pairs_fail_fast
    (v w : Z) (Hv : v < 10) (Hw : w < 10) (Hv0 : 0 <= v) (Hw0 : 0 <= w) : True.
Proof.
  Fail assert (Hpackage : source_match_commit_pairs 0)
    by (unfold source_match_commit_pairs; do 20 eexists; source_match_commit_goal).
  exact I.
Qed.

Lemma source_match_commit_pairs_positive
    (v w : Z) (Hv : v < 10) (Hw : w < 10) (Hv0 : 0 <= v) (Hw0 : 0 <= w) (Hneg : -1 < 0) :
  source_match_commit_pairs (-1).
Proof.
  unfold source_match_commit_pairs; do 20 eexists; source_match_commit_goal;
  repeat split; assumption.
Qed.

(* The shared evar first meets [u], which the later fact refuses; the matcher
   must backtrack to [v]. *)
Lemma source_match_shared_evar_backtracks
    (P : Z -> Prop) (v u : Z) (Hv : v < 10) (Hu : u < 10) (HP : P v) :
  exists a, a < 10 /\ P a.
Proof.
  eexists; source_match_commit_goal; split; assumption.
Qed.

(* The evar also occurs outside the requested fact: no commit, so a refusal
   in [finish] backtracks to the next candidate. *)
Lemma source_match_outside_evar_backtracks
    (P : Z -> Prop) (v u : Z) (Hv : v < 10) (Hu : u < 10) (HP : P v) :
  exists a, a < 10 /\ P a.
Proof.
  eexists;
  lazymatch goal with
  | |- ?left /\ _ =>
      ZesuSsz.Automation2.SourceFactMatching.zesu_source_match_fact left
        ltac:(split; [assumption | assumption])
  end.
Qed.

(* A committed segment does not hide a later refusal. *)
Lemma source_match_commit_refusal (v : Z) (Hv : v < 10) (Hv0 : 0 <= v) : True.
Proof.
  Fail assert (Hpackage : exists a, a < 10 /\ 0 <= a /\ 0 < 0)
    by (eexists; source_match_commit_goal).
  exact I.
Qed.
