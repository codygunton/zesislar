Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.WitnessScopeCarrier.

Lemma witness_scope_no_transitive_activation : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepListWitness) in idtac.
  Fail let _ := constr:(_ : ZesuStepTupleWitness) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.ListWitness.
Require Import ZesuSsz.Automation.Switches.TupleWitness.

Lemma witness_scope_direct_activation : True.
Proof.
  let _ := constr:(_ : ZesuStepListWitness) in idtac.
  let _ := constr:(_ : ZesuStepTupleWitness) in idtac.
  exact I.
Qed.
