Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.DecodeItem.Join6ae0.Branch.
Require Import ZesuSsz.Proofs.DecodeItem.Join6ae0.From69e0.
Require Import ZesuSsz.Proofs.DecodeItem.Join6ae0.From6a6c.
Require Import ZesuSsz.Proofs.DecodeItem.Prologue.

Lemma switch_scope_shared_importers : True.
Proof.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepRecordWitness) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.ByteArrays.ZesuStepWordArrayHandoff) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepInstructionLookup) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepStackWrite) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.Hooks.ZesuStepRamFault) in idtac.
  Fail let _ := constr:(_ : ZesuSsz.Automation.BitvectorFacts.ZesuStepLowMask) in idtac.
  exact I.
Qed.
