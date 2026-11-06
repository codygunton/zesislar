Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.PureFactHints.

(* Remove the release instances locally to preserve the isolation refusal. *)
Section ReleaseSwitchIsolation.
#[local] Remove Hints
  ZesuSsz.Automation.Switches.PureFactHints.zesu_switch_pure_fact_hints : typeclass_instances.

Lemma pure_hint_import_isolation : True.
Proof.
  Fail zesu_switch_enabled constr:(ZesuSsz.Automation.Hooks.ZesuStepPureFactHints).
  Fail let _ := constr:(_ : ZesuStepPureFactHints) in idtac.
  Fail zesu_pure_fact_hints_if_enabled.
  exact I.
Qed.

End ReleaseSwitchIsolation.
Require Import ZesuSsz.Automation.All.
