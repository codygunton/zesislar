From Coq Require Import ZArith.ZArith.
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
