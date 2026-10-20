Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.

Record DerivedFinishFixture := {
  fixtureSource : Prop;
  fixtureResult : nat -> Prop;
  fixtureSeed : nat;
  fixtureDerive : fixtureSource ->
    forall index : nat, index = fixtureSeed -> fixtureResult index;
  fixtureOpen : Prop;
  fixtureOpenProof : fixtureOpen
}.

Record MissingFinishFixture := {
  missingSource : Prop;
  missingResult : nat -> Prop;
  missingSeed : nat
}.

#[local] Instance fixtureDerivedRule (fixture : DerivedFinishFixture) :
  ZesuDerivedFacts (fixtureSource fixture)
    (forall index : nat, index = fixtureSeed fixture -> fixtureResult fixture index) :=
  fixtureDerive fixture.

Lemma derivedFinishCloses (fixture : DerivedFinishFixture) :
  fixtureSource fixture -> fixtureSeed fixture = fixtureSeed fixture ->
  fixtureResult fixture (fixtureSeed fixture).
Proof.
  intros Hsource Hself.
  Fail solve [zesu_finish_pure_goal_base].
  zesu_finish_pure_goal.
Qed.

Lemma derivedFinishMissing (fixture : MissingFinishFixture) :
  missingSource fixture -> missingSeed fixture = missingSeed fixture -> True.
Proof.
  intros Hsource Hself.
  Fail assert (Hmissing : missingResult fixture (missingSeed fixture))
    by solve [zesu_finish_pure_goal].
  exact I.
Qed.

Lemma derivedFinishOpenRetainsOnce (fixture : DerivedFinishFixture) :
  fixtureSource fixture -> fixtureOpen fixture.
Proof.
  intro Hsource.
  zesu_finish_pure_goal.
  lazymatch goal with
  | _ : (forall index : nat, index = fixtureSeed fixture -> fixtureResult fixture index) |- _ => idtac
  end.
  Fail progress zesu_saturate_derived_facts.
  exact (fixtureOpenProof fixture).
Qed.

Print Assumptions derivedFinishCloses.
Print Assumptions derivedFinishMissing.
Print Assumptions derivedFinishOpenRetainsOnce.
