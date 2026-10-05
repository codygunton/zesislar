Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.ArrayRegionBounds.

Lemma array_region_no_transitive_activation : True.
Proof.
  Fail let enabled := constr:(_ : ZesuStepArrayRegionBounds) in idtac.
  exact I.
Qed.
