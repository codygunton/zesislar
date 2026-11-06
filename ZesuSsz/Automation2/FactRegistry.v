Require ZesuSsz.Automation.FactRegistry.
From lithium Require Import simpl_classes.
From stdpp Require Import tactics.
Definition zesu_simpl_and_fact {P : Prop} (proof : P) : SimplAnd P True :=
  conj (fun _ : True => proof) (fun _ : P => I).
(* TCFastDone alone can instantiate a bare proposition evar.
   Hint Mode ! preserves refusal for that evar. *)
#[global] Hint Mode ZesuSsz.Automation.FactRegistry.ZesuFactEvidence ! : typeclass_instances.
#[global] Instance zesu_fact_evidence_fast_done (P : Prop) (proof : TCFastDone P) :
  ZesuSsz.Automation.FactRegistry.ZesuFactEvidence P := @ZesuSsz.Automation.FactRegistry.Build_ZesuFactEvidence P proof.
