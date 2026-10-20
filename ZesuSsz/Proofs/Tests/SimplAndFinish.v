Require Import ZesuSsz.Automation.All.
From lithium Require Import simpl_classes.
Require Import ZesuSsz.Proofs.Tests.DerivedFactFinish.

#[local] Instance registeredLeafRule (fixture : DerivedFinishFixture) :
  SimplAnd (fixtureOpen fixture) True.
Proof.
  unfold SimplAnd. split.
  - intros _. exact (fixtureOpenProof fixture).
  - intros _. exact I.
Qed.

Lemma registeredLeafFinishes (fixture : DerivedFinishFixture) :
  fixtureOpen fixture.
Proof.
  Fail solve [zesu_finish_pure_goal_base].
  zesu_finish_pure_goal.
Qed.

Lemma missingLeafRefuses (fixture : MissingFinishFixture) : True.
Proof.
  Fail assert (Hmissing : missingResult fixture (missingSeed fixture))
    by solve [zesu_finish_simpl_and_leaf].
  Fail assert (Hmissing : missingResult fixture (missingSeed fixture))
    by solve [zesu_finish_pure_goal].
  exact I.
Qed.

Print Assumptions registeredLeafRule.
Print Assumptions registeredLeafFinishes.
Print Assumptions missingLeafRefuses.

Definition registeredStructuredLeaf (fixture : DerivedFinishFixture) : Prop :=
  fixtureResult fixture (fixtureSeed fixture) /\ fixtureOpen fixture.

#[local] Instance registeredStructuredRule (fixture : DerivedFinishFixture)
    (Hsource : fixtureSource fixture) :
  SimplAnd (registeredStructuredLeaf fixture) True.
Proof.
  unfold SimplAnd, registeredStructuredLeaf. split.
  - intros _. split.
    + apply (fixtureDerive fixture Hsource). reflexivity.
    + exact (fixtureOpenProof fixture).
  - intros _. exact I.
Qed.

#[local] Hint Extern 0 (SimplAnd (registeredStructuredLeaf ?fixture) True) =>
  match goal with
  | Hsource : fixtureSource fixture |- _ =>
      exact (registeredStructuredRule fixture Hsource)
  end : typeclass_instances.

Lemma registeredConjunctionFinishes (fixture : DerivedFinishFixture) (P : Prop) :
  fixtureSource fixture -> P -> P /\ registeredStructuredLeaf fixture.
Proof.
  intros Hsource HP.
  Fail solve [zesu_finish_pure_goal_base].
  zesu_finish_pure_goal.
Qed.
Print Assumptions registeredConjunctionFinishes.
