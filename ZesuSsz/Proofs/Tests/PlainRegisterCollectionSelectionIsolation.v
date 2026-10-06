Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.PlainRegisterCollectionSelection.

Lemma plain_register_selection_no_transitive_activation : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepRegisterCollectionSelection) in idtac.
  exact I.
Qed.
