Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Definition exitMeaningOffSource {Sigma} (facts : Prop)
    (resource : iProp Sigma) : iProp Sigma := (⌜facts⌝ ∗ resource)%I.
Global Instance : LithiumUnfold (@exitMeaningOffSource) := I.
Global Typeclasses Opaque exitMeaningOffSource.

#[local] Instance exitMeaningOffEvidence {Sigma} (facts : Prop)
    (resource : iProp Sigma) :
    ZesuExitMeaning (exitMeaningOffSource facts resource) facts.
Proof.
  rewrite /ZesuExitMeaning /exitMeaningOffSource.
  iIntros "[%Hfacts _]". done.
Qed.

Lemma exitMeaningOff (Sigma : gFunctors) (facts : Prop)
    (resource : iProp Sigma) : True.
Proof.
  Fail assert (Henabled : ZesuStepExitMeaning) by typeclasses eauto.
  Fail zesu_entry_intro_goal_exit_registration constr:(Sigma)
    constr:(exitMeaningOffSource facts resource)
    ltac:(fun facts evidence marker => idtac).
  exact I.
Qed.

Print Assumptions exitMeaningOff.
