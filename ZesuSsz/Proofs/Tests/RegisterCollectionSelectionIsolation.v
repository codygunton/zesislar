Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.RegisterCollectionSelection.

(* Remove the release instances locally to preserve the isolation refusal. *)
Section ReleaseSwitchIsolation.
#[local] Remove Hints
  ZesuSsz.Automation.Switches.RegisterCollectionSelection.zesu_register_collection_selection_enabled : typeclass_instances.

Lemma register_selection_no_transitive_activation : True.
Proof.
  Fail zesu_switch_enabled constr:(ZesuSsz.Automation.Hooks.ZesuStepRegisterCollectionSelection).
  Fail let _ := constr:(_ : ZesuStepRegisterCollectionSelection) in idtac.
  exact I.
Qed.

End ReleaseSwitchIsolation.
Require Import ZesuSsz.Automation.All.
