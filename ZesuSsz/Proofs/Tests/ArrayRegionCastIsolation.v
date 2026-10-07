Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.ArrayRegionCast.

Lemma array_region_cast_no_transitive_activation : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepArrayRegionBounds) in idtac.
  exact I.
Qed.
