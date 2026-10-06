Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.PureWitnessConstraints.

Lemma pure_constraints_no_transitive_activation : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepPureWitnessConstraints) in idtac.
  exact I.
Qed.
