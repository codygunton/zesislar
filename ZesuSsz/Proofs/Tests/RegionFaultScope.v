Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.RegionFaultScopeCarrier.

Lemma region_fault_no_transitive_activation : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepRegionFault) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.RegionFault.

Lemma region_fault_direct_activation : True.
Proof.
  let _ := constr:(_ : ZesuStepRegionFault) in idtac.
  exact I.
Qed.
