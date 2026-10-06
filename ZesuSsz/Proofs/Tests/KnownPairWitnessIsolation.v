Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.KnownPairWitness.

Lemma known_pair_no_transitive_activation : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepKnownPairWitness) in idtac.
  exact I.
Qed.
