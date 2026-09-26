Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ReturnBundle.

Goal True.
  Fail let enabled := constr:(_ : ZesuStepReturnBundle) in idtac.
  exact I.
Qed.
