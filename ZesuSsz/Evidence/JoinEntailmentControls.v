Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.JoinEntailment.
From stdpp Require Import decidable.

Section Projection.
Variables P Q R : Prop.
Definition join_projection_alias : Prop := P /\ Q /\ R.

Lemma join_projection_positive (Hsource : join_projection_alias) : P /\ Q /\ R.
Proof.
  repeat JoinEntailment.zesu_join_project_once.
  repeat split; assumption.
Qed.

Lemma join_projection_preserves_source (Hsource : join_projection_alias) :
  join_projection_alias.
Proof.
  repeat JoinEntailment.zesu_join_project_once.
  exact Hsource.
Qed.

Lemma join_projection_atomic_refuses (Hsource : P) : True.
Proof.
  Fail JoinEntailment.zesu_join_project_once.
  exact I.
Qed.

Lemma join_duplicate_fact_refuses (Hsource : P) : True.
Proof.
  Fail JoinEntailment.zesu_join_add_fact constr:(Hsource).
  exact I.
Qed.
End Projection.

Section BooleanViews.
Variable P : Prop.
Context `{!Decision P}.

Lemma join_boolean_positive (Hsource : bool_decide P = true) : P.
Proof.
  JoinEntailment.zesu_join_boolean_once.
  Fail JoinEntailment.zesu_join_boolean_once.
  assumption.
Qed.

Lemma join_boolean_negative (Hsource : negb (bool_decide P) = true) : ~ P.
Proof.
  JoinEntailment.zesu_join_boolean_once.
  Fail JoinEntailment.zesu_join_boolean_once.
  assumption.
Qed.
End BooleanViews.
