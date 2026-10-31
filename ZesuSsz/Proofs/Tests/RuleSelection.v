Require Import ZesuSsz.Automation.All.

Section MissingSelection.
  #[local] Remove Hints ZesuSsz.Automation.All.zesu_explicit_v1 : typeclass_instances.

  Lemma missing_rule_selection_refuses : True.
  Proof.
    Fail zesu_with_rule_set ltac:(exact I) ltac:(exact I).
    exact I.
  Qed.
End MissingSelection.

Lemma explicit_v1_selection : True.
Proof.
  zesu_with_rule_set ltac:(exact I) ltac:(fail 0 "unexpected v2").
Qed.

Section SelectedV2.
  #[local] Instance selected_v2 : ZesuSsz.Automation.PureFacts.ZesuRuleSetV2 := I.

  Lemma explicit_v2_has_priority : True.
  Proof.
    zesu_with_rule_set ltac:(fail 0 "unexpected v1") ltac:(exact I).
  Qed.

  Lemma selected_v2_failure_does_not_select_v1 : True.
  Proof.
    Fail zesu_with_rule_set ltac:(exact I) ltac:(fail 0 "selected v2 failed").
    exact I.
  Qed.
End SelectedV2.
