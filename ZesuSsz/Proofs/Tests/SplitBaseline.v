From Coq Require Import ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The pre-check of the split-conjunct finisher: only the facts after the
   baseline marker count, and one of them must share an atom with the goal. *)
Lemma split_baseline_new_fact_reaches_goal (x y : Z) :
  x < 5 -> ZesuSsz.Automation2.Finish.zesu_split_baseline -> y < 3 -> x + y < 8 -> x < 10.
Proof.
  intros Hx Hbaseline Hy Hsum.
  ZesuSsz.Automation2.ContextCollection.zesu_facts_after_share_term
    constr:(ZesuSsz.Automation2.Finish.zesu_split_baseline).
  lia.
Qed.

Lemma split_baseline_no_new_fact_reaches_goal (x y : Z) :
  x < 5 -> ZesuSsz.Automation2.Finish.zesu_split_baseline -> y < 3 -> x < 10.
Proof.
  intros Hx Hbaseline Hy.
  Fail ZesuSsz.Automation2.ContextCollection.zesu_facts_after_share_term
    constr:(ZesuSsz.Automation2.Finish.zesu_split_baseline).
  lia.
Qed.

(* Without a baseline every fact counts as new. *)
Lemma split_baseline_absent (x : Z) : x < 5 -> x < 10.
Proof.
  intros Hx.
  ZesuSsz.Automation2.ContextCollection.zesu_facts_after_share_term
    constr:(ZesuSsz.Automation2.Finish.zesu_split_baseline).
  lia.
Qed.

(* A closed goal has no atoms and needs no new fact: the pre-check lets the
   finisher run on it (the split conjunct left open in berlinGasCalc 3d20). *)
Lemma split_baseline_closed_goal (x : Z) :
  x < 5 -> ZesuSsz.Automation2.Finish.zesu_split_baseline ->
  bv_unsigned (6148914691236517205%bv : bv 64) >= bv_unsigned (33%bv : bv 64).
Proof.
  intros Hx Hbaseline.
  ZesuSsz.Automation2.ContextCollection.zesu_facts_after_share_term
    constr:(ZesuSsz.Automation2.Finish.zesu_split_baseline).
  bv_solve.
Qed.
