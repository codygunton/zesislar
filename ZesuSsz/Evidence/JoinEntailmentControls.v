Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.JoinEntailment.
From Coq Require Import ZArith.ZArith.
Require Import stdpp.bitvector.definitions.
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

Open Scope Z_scope.

Section NarrowClass.
Variables (value lower upper : Z).

Lemma join_class_narrow_positive
    (Hlower : lower <= value) (Hupper : value <= upper)
    (Hdifferent : value <> lower) : lower + 1 <= value <= upper.
Proof. JoinEntailment.zesu_join_class_side. Qed.

Lemma join_class_missing_upper_refuses
    (Hlower : lower <= value) (Hdifferent : value <> lower) : True.
Proof.
  Fail assert (lower + 1 <= value <= upper) by
    JoinEntailment.zesu_join_class_side.
  exact I.
Qed.

Lemma join_class_missing_disequality_refuses
    (Hlower : lower <= value) (Hupper : value <= upper) : True.
Proof.
  Fail assert (lower + 1 <= value <= upper) by
    JoinEntailment.zesu_join_class_side.
  exact I.
Qed.

Lemma join_class_changed_value_refuses (other : Z)
    (Hlower : lower <= other) (Hupper : other <= upper)
    (Hdifferent : other <> lower) : True.
Proof.
  Fail assert (lower + 1 <= value <= upper) by
    JoinEntailment.zesu_join_class_side.
  exact I.
Qed.
End NarrowClass.

Lemma join_class_closed_width_view (word : bv 8) (lower upper : Z)
    (Hlower : lower <= @bv_unsigned 8 word)
    (Hupper : @bv_unsigned 8 word <= upper)
    (Hdifferent : @bv_unsigned 8 word <> lower) :
    lower + 1 <= @bv_unsigned (Z.to_N 8) word <= upper.
Proof. JoinEntailment.zesu_join_class_side. Qed.
