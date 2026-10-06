Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.ArrayRegionSearch.

Lemma array_region_search_no_transitive_activation : True.
Proof.
  Fail let enabled := constr:(_ : ZesuStepArrayRegionBounds) in idtac.
  exact I.
Qed.
