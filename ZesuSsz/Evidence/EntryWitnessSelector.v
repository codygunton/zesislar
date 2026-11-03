Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Evidence.Block2Core.
Require Import ZesuSsz.Automation.ExplicitWitnessOrder293.
From lithium Require Import lvar interpreter base pure_definitions.
From iris.proofmode Require Import environments.
Set Default Proof Mode "Classic".

(* This registry contains choices, not facts about the requested assertion. *)
Class ZesuEntryWitnessChoice {Key : Type} (key : Key) (Witness : Type) := {
  zesu_entry_witness_choice : Witness
}.
#[global] Hint Mode ZesuEntryWitnessChoice + + - : typeclass_instances.

(* Constructible metadata adds no logical premise to the requested proof. *)
Inductive ZesuEntryWitnessPending {Key Witness : Type}
    (key : Key) (data : Witness) : Prop :=
  ZesuEntryWitnessPendingHere.

Ltac zesu_entry_witness_capture key :=
  tryif ZesuSsz.Evidence.Block2Core.block2_has_unresolved key then fail 100 "The successor key is unresolved." else idtac;
  tryif match goal with
    | _ : ZesuEntryWitnessPending key _ |- _ => idtac
    end then fail 0 "The successor key is already retained." else idtac;
  let registration := constr:(_ : ZesuEntryWitnessChoice key _) in
  let registration_type := type of registration in
  tryif ZesuSsz.Evidence.Block2Core.block2_has_unresolved registration then fail 100 "The registered choice is unresolved." else idtac;
  tryif ZesuSsz.Evidence.Block2Core.block2_has_unresolved registration_type then fail 100 "The registered choice type is unresolved." else idtac;
  lazymatch registration_type with
  | @ZesuEntryWitnessChoice ?Key key ?Witness =>
      let data := constr:(@zesu_entry_witness_choice Key key Witness registration) in
      let marker := fresh "HentryWitnessPending" in
      pose proof (@ZesuEntryWitnessPendingHere Key Witness key data) as marker
  end.

Ltac zesu_entry_witness_consume :=
  lazymatch goal with
  | marker : @ZesuEntryWitnessPending _ _ _ ?data
    |- environments.envs_entails _ (@bi_exist _ (li_prod _ _) _) =>
      (* Invalid registered choices must not enter the ordinary fallback. *)
      tryif (first [zesu_apply_lithium_witnesses data])
      then clear marker
      else fail 100 "The registered witness tuple does not match the remaining target."
  end.

(* Capture can fail only when no registration applies. Invalid data is fatal. *)
Ltac zesu_entry_witness_before key continuation :=
  first [zesu_entry_witness_capture key | idtac];
  continuation.
