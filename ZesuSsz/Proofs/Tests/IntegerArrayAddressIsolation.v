Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.IntegerArrayAddress.

Lemma integer_array_address_import_isolation : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepIntegerArrayAddress) in idtac.
  exact I.
Qed.
