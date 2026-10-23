From lithium Require Import simpl_classes.
From stdpp Require Import tactics.
Definition zesu_simpl_and_fact {P : Prop} (proof : P) : SimplAnd P True :=
  conj (fun _ : True => proof) (fun _ : P => I).
Class ZesuFactEvidence (P : Prop) : Prop := {
  zesu_fact_evidence : P
}.
(* TCFastDone alone can instantiate a bare proposition evar.
   Hint Mode ! preserves refusal for that evar. *)
#[global] Hint Mode ZesuFactEvidence ! : typeclass_instances.
#[global] Instance zesu_fact_evidence_fast_done (P : Prop) (proof : TCFastDone P) :
  ZesuFactEvidence P := @Build_ZesuFactEvidence P proof.
