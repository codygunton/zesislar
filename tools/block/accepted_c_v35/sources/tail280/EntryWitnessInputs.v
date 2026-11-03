Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Evidence.Block2Core.
Require Import ZesuSsz.Evidence.EntryWitnessSelector.
Require Import ZesuSsz.Automation.EntryWitnessProfile.
From Coq Require Import Strings.String NArith.NArith.
From iris.proofmode Require Import environments.
From lithium Require Import lvar interpreter base pure_definitions.
Set Default Proof Mode "Classic".

Inductive ZesuWitnessInput : Type -> Type :=
  | ZesuWitnessUnit : ZesuWitnessInput unit
  | ZesuWitnessRegister (width : N) (register : string) : ZesuWitnessInput (bv width)
  | ZesuWitnessPair {A B : Type} :
      ZesuWitnessInput A -> ZesuWitnessInput B -> ZesuWitnessInput (A * B).

(* A mapping selects values. It proves no assertion about those values. *)
Class ZesuEntryWitnessMapping {Key : Type} (key : Key) (Input Witness : Type) := {
  zesu_witness_input : ZesuWitnessInput Input;
  zesu_witness_mapping : Input -> Witness
}.
#[global] Hint Mode ZesuEntryWitnessMapping + + - - : typeclass_instances.

Ltac zesu_witness_resolved term :=
  tryif ZesuSsz.Evidence.Block2Core.block2_has_unresolved term
  then fail 100 "The entry witness input contains an unresolved evar."
  else idtac.

Ltac zesu_witness_read_input source continuation :=
  let source := eval hnf in source in
  lazymatch source with
  | ZesuWitnessUnit => continuation constr:(tt)
  | @ZesuWitnessPair ?A ?B ?left ?right =>
      zesu_witness_read_input left ltac:(fun first =>
        zesu_witness_read_input right ltac:(fun second =>
          continuation constr:((first, second))))
  | ZesuWitnessRegister ?width ?register =>
      zesu_witness_resolved width;
      zesu_witness_resolved register;
      let visit := ltac:(fun name resource =>
        lazymatch resource with
        | (?actual_register ↦ᵣ RVal_Bits (@stdpp.bitvector.definitions.bv_to_bvn ?actual_width ?word))%I =>
            constr_eq actual_register register;
            zesu_witness_resolved actual_width;
            unify actual_width width;
            let actual_type := type of word in
            let expected_type := constr:(bv width) in
            unify actual_type expected_type;
            zesu_witness_resolved word;
            continuation word
        end) in
      lazymatch goal with
      | |- environments.envs_entails ?environment _ =>
          let environment := eval hnf in environment in
          lazymatch environment with
          | environments.Envs ?persistent ?spatial _ =>
              let rec scan entries :=
                let entries := eval hnf in entries in
                lazymatch entries with
                | environments.Esnoc ?remaining ?name ?resource =>
                    first [visit name resource | scan remaining]
                end in
              first [scan spatial | scan persistent]
          end
      end
  end.

Ltac zesu_entry_mapping_capture key :=
  zesu_witness_resolved key;
  tryif match goal with
    | _ : ZesuEntryWitnessPending key _ |- _ => idtac
    end then fail 0 else idtac;
  let registration := constr:(_ : ZesuEntryWitnessMapping key _ _) in
  let registration_type := type of registration in
  lazymatch registration_type with
  | @ZesuEntryWitnessMapping ?Key ?registered_key ?Input ?Witness =>
      let requested_head := get_head key in
      let registered_head := get_head registered_key in
      constr_eq requested_head registered_head;
      zesu_witness_resolved registration;
      zesu_witness_resolved registration_type;
      let input_source := constr:(@zesu_witness_input Key key Input Witness registration) in
      let mapping := constr:(@zesu_witness_mapping Key key Input Witness registration) in
      tryif zesu_witness_read_input input_source ltac:(fun inputs =>
        let data := constr:(mapping inputs) in
        zesu_witness_resolved data;
        let marker := fresh "HentryWitnessPending" in
        pose proof (@ZesuEntryWitnessPendingHere Key Witness key data) as marker)
      then idtac
      else fail 100 "The registered predecessor input is not owned."
  end.

(* Run before the stock step can unfold the requested entry. *)
Ltac zesu_entry_mapping_capture_goal :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_sep _ ?requested _) =>
      tryif ZesuSsz.Evidence.Block2Core.block2_has_unresolved requested
      then fail 0 else zesu_entry_mapping_capture requested
  | |- environments.envs_entails _ ?requested =>
      tryif ZesuSsz.Evidence.Block2Core.block2_has_unresolved requested
      then fail 0 else zesu_entry_mapping_capture requested
  end.

(* Exact metadata and pure/frame readiness precede the unchanged selector. *)
Ltac zesu_entry_mapping_consume_ready :=
  lazymatch goal with
  | _ : @ZesuEntryWitnessPending _ ?Witness ?key _
    |- environments.envs_entails _ (@bi_exist _ (li_prod ?A ?B) ?body) =>
      EntryWitnessProfile.zesu_entry_witness_ready key Witness constr:(li_prod A B) body;
      zesu_entry_witness_consume
  end.
