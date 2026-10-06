Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Hooks.
Lemma region_normalization_disabled : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepRegionFaultNormalization) in idtac.
  exact I.
Qed.
