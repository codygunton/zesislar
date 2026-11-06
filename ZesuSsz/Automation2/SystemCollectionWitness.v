Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.ResourceGroups.
From Coq Require Import Lists.List String.
From stdpp Require Import list bitvector.definitions.
Import ListNotations.

Class ZesuStepSystemCollectionWitness : Prop := {}.

(* The witness comes from the selected cell; its original owner is restored. *)
Lemma zesu_reg_col_shape_view `{!islaG Sigma} `{!threadG}
    (registers : list (reg_kind * valu_shape)) (index : nat)
    (slot : reg_kind * valu_shape) :
  registers !! index = Some slot ->
  reg_col registers -∗ ∃ value,
    ⌜valu_has_shape value slot.2⌝ ∗ reg_col registers.
Proof.
  intros Hlookup. iIntros "Hregisters".
  iDestruct (reg_col_lookup with "Hregisters") as (value Hshape) "[Hcell Hrest]";
    [exact Hlookup|].
  iExists value. iSplit; [done|].
  iApply reg_col_lookup; [exact Hlookup|].
  iExists value. iFrame. done.
Qed.

(* Reuse the public struct view, retaining the exact field-value equation. *)
Lemma zesu_single_field_shape_view (value : valu) (field : string) (shape : valu_shape) :
  valu_has_shape value (StructShape [(field, shape)]) ->
  ∃ field_value,
    value = RegVal_Struct [(field, field_value)] /\ valu_has_shape field_value shape.
Proof.
  intros Hshape.
  pose proof (simpl_impl_valu_struct_shape value [(field, shape)]) as Hview.
  change (valu_has_shape value (StructShape [(field, shape)]) ->
    ∃ field_value, valu_has_shape field_value shape /\
      value = RegVal_Struct [(field, field_value)]) in Hview.
  destruct (Hview Hshape) as [field_value [Hfield Hvalue]].
  exists field_value. split; assumption.
Qed.

Ltac zesu_source_bits_view value shape_proof continuation :=
  lazymatch type of shape_proof with
  | valu_has_shape ?actual ?shape =>
      constr_eq actual value;
      let normalized := eval cbv beta iota zeta delta [snd] in shape in
      change (valu_has_shape value normalized) in shape_proof
  end;
  lazymatch type of shape_proof with
  | valu_has_shape value (BitsShape ?width) =>
      let word := fresh "sourceWord" in
      let Heq := fresh "HsourceValue" in
      destruct (valu_has_bits_shape value width shape_proof) as [word Heq];
      continuation word
  | valu_has_shape value (MaskShape ?width ?mask ?expected) =>
      let word := fresh "sourceWord" in
      let Heq := fresh "HsourceValue" in
      let Hmask := fresh "HsourceMask" in
      destruct (valu_has_mask_shape value width mask expected shape_proof)
        as [word [Heq Hmask]];
      continuation word
  | valu_has_shape value (StructShape [(?field, ?shape)]) =>
      let field_value := fresh "sourceField" in
      let Hcontainer := fresh "HsourceStruct" in
      let Hfield := fresh "HsourceField" in
      destruct (zesu_single_field_shape_view value field shape shape_proof)
        as [field_value [Hcontainer Hfield]];
      zesu_source_bits_view field_value Hfield continuation
  end.

Ltac zesu_system_collection_witness collection index slot continuation :=
  SwitchDispatch.zesu_switch_enabled constr:(ZesuStepSystemCollectionWitness);
  iMatchHyp ltac:(fun Hcollection body =>
    lazymatch body with
    | reg_col ?actual =>
        constr_eq actual collection;
        let Hlookup := fresh "HsourceLookup" in
        assert (Hlookup : collection !! index = Some slot) by reflexivity;
        let value := fresh "sourceValue" in
        let Hshape := fresh "HsourceShape" in
        iDestruct (zesu_reg_col_shape_view collection index slot Hlookup with Hcollection)
          as (value Hshape) Hcollection;
        zesu_source_bits_view value Hshape continuation
    end).
