Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.PureFactHints.

Lemma pure_hint_import_isolation : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepPureFactHints) in idtac.
  Fail zesu_pure_fact_hints_if_enabled.
  exact I.
Qed.
