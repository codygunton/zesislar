Require Import ZesuSsz.Automation2.EntryWitnessReadiness.
From Coq Require Import Strings.String.
From lithium Require Import lvar interpreter base pure_definitions.

(* Names come from authenticated declaration metadata, not erased li_prod values. *)
Inductive ZesuWitnessProfile : Type :=
  | ZesuWitnessProfileEnd : ZesuWitnessProfile
  | ZesuWitnessProfileSlot (name : string) (kind : Type)
      (remaining : ZesuWitnessProfile) : ZesuWitnessProfile.

Class ZesuEntryWitnessSourceProfile {Key : Type} (key : Key) (Witness : Type) := {
  zesu_source_profile_declaration : string;
  zesu_source_profile_slots : ZesuWitnessProfile
}.
#[global] Hint Mode ZesuEntryWitnessSourceProfile + + + : typeclass_instances.

Class ZesuEntryWitnessDataProfile {Key : Type} (key : Key) (Witness : Type) := {
  zesu_data_profile_declaration : string;
  (* This hash binds the emitted mapping fragment before its metadata records. *)
  zesu_data_profile_mapping : string;
  zesu_data_profile_slots : ZesuWitnessProfile
}.
#[global] Hint Mode ZesuEntryWitnessDataProfile + + + : typeclass_instances.

Ltac zesu_witness_profile_compare source data :=
  let source := eval hnf in source in
  let data := eval hnf in data in
  lazymatch source with
  | ZesuWitnessProfileEnd => constr_eq data source
  | ZesuWitnessProfileSlot ?name ?kind ?remaining =>
      lazymatch data with
      | ZesuWitnessProfileSlot ?actual_name ?actual_kind ?actual_remaining =>
          constr_eq name actual_name;
          constr_eq kind actual_kind;
          zesu_witness_profile_compare remaining actual_remaining
      end
  end.

Ltac zesu_witness_profile_external profile witness_type accumulated continuation :=
  let profile := eval hnf in profile in
  let witness_type := eval hnf in witness_type in
  lazymatch profile with
  | ZesuWitnessProfileEnd =>
      constr_eq witness_type constr:(unit);
      continuation accumulated
  | ZesuWitnessProfileSlot ?name ?kind ?remaining =>
      lazymatch witness_type with
      | (?actual * ?tail)%type =>
          constr_eq kind actual;
          zesu_witness_profile_external remaining tail
            constr:(ZesuWitnessProfileSlot name kind accumulated) continuation
      end
  end.

Ltac zesu_witness_profile_internal profile target_type :=
  let profile := eval hnf in profile in
  lazymatch profile with
  | ZesuWitnessProfileEnd => constr_eq target_type constr:(unit)
  | ZesuWitnessProfileSlot _ ?kind ?remaining =>
      lazymatch target_type with
      | li_prod ?actual ?tail =>
          constr_eq kind actual;
          zesu_witness_profile_internal remaining tail
      end
  end.

(* Reverse only the metadata view. The existing selector reverses data once. *)
Ltac zesu_entry_witness_profile_check source data Witness target_type :=
  tryif has_evar source then fail 1 "The source profile is unresolved." else idtac;
  tryif has_evar data then fail 1 "The data profile is unresolved." else idtac;
  tryif has_evar target_type then fail 1 "The target profile is unresolved." else idtac;
  zesu_witness_profile_compare source data;
  zesu_witness_profile_external source Witness constr:(ZesuWitnessProfileEnd)
    ltac:(fun internal => zesu_witness_profile_internal internal target_type).

Ltac zesu_entry_witness_ready key Witness target_type body :=
  let source := constr:(_ : ZesuEntryWitnessSourceProfile key Witness) in
  let data := constr:(_ : ZesuEntryWitnessDataProfile key Witness) in
  tryif has_evar source then fail 1 "The source profile is unresolved." else idtac;
  tryif has_evar data then fail 1 "The data profile is unresolved." else idtac;
  let declaration := eval hnf in
    (@zesu_source_profile_declaration _ key Witness source) in
  let actual_declaration := eval hnf in
    (@zesu_data_profile_declaration _ key Witness data) in
  constr_eq declaration actual_declaration;
  tryif constr_eq declaration constr:(EmptyString)
    then fail 1 "The declaration hash is absent." else idtac;
  let mapping := eval hnf in
    (@zesu_data_profile_mapping _ key Witness data) in
  tryif constr_eq mapping constr:(EmptyString)
    then fail 1 "The mapping hash is absent." else idtac;
  let expected := constr:(@zesu_source_profile_slots _ key Witness source) in
  let emitted := constr:(@zesu_data_profile_slots _ key Witness data) in
  zesu_entry_witness_profile_check expected emitted Witness target_type;
  EntryWitnessReadiness.zesu_entry_witness_body_ready body.
