From Coq Require Import Lists.List ZArith.ZArith.
From Ltac2 Require Import Ltac2.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.EvmSailAdapter.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Evidence.SignatureAxiomAllowlist.

Open Scope Z_scope.
Import ListNotations.

Declare ML Module "zesu-signature-gates.plugin".

Ltac2 @ external exact_axioms : constr -> constr list -> unit :=
  "zesu-signature-gates.plugin" "exact_axioms".

(* A closed control theorem tests the type and axiom gates. *)
Definition ReviewedControlType : Prop :=
  forall bytes : list nat, bytes = bytes.

Theorem reviewed_control : ReviewedControlType.
Proof. unfold ReviewedControlType; intros; reflexivity. Qed.

Check (@reviewed_control : ReviewedControlType).
Print Assumptions reviewed_control.
Ltac2 Eval exact_axioms 'reviewed_control (approved_library_axioms ()).

Definition ReviewedRlpItemType : Type :=
  forall base len : Z, list byte -> RlpCursor base len ->
  SailOutcome
    ({full_len & {content_len & RlpFieldRef base full_len content_len}}%type) -> Prop.

Definition ReviewedRlpHeaderType : Type :=
  forall base len : Z, list byte -> StatelessInputSliceFields base len ->
  SailOutcome (bool * source_pointer * Z) -> Prop.

Definition ReviewedRlpNodeType : Type :=
  forall base len : Z, list byte -> StatelessInputSliceFields base len ->
  SailOutcome
    ({source_len & {source_off & RlpCursor source_off source_len}}%type) -> Prop.

Definition ReviewedParentHeaderFieldsType : Type :=
  forall base len : Z, list byte -> StatelessInputSliceFields base len ->
  parent_header_field_cursor -> ParentHeaderFields ->
  SailOutcome ParentHeaderFields -> Prop.

Check (@ReferenceRlpItem : ReviewedRlpItemType).
Check (@ReferenceRlpHeader : ReviewedRlpHeaderType).
Check (@ReferenceRlpNode : ReviewedRlpNodeType).
Check (@ReferenceParentHeaderFields : ReviewedParentHeaderFieldsType).

(* Definition equality pins the input domain, generated action, initialized
   register state, evaluator, and complete outcome relation. *)
Definition ReviewedRlpItemRelation {base len : Z}
    (bytes : list byte) (cursor : RlpCursor base len)
    (outcome : SailOutcome
      ({full_len & {content_len & RlpFieldRef base full_len content_len}}%type))
    : Prop :=
  validInputSlice bytes base len = true /\
  runRlpDecodeItem bytes cursor = outcome.

Definition ReviewedRlpHeaderRelation {base len : Z}
    (bytes : list byte) (cursor : StatelessInputSliceFields base len)
    (outcome : SailOutcome (bool * source_pointer * Z)) : Prop :=
  validInputSlice bytes base len = true /\
  runRlpRefHdr bytes cursor = outcome.

Definition ReviewedRlpNodeRelation {base len : Z}
    (bytes : list byte) (node : StatelessInputSliceFields base len)
    (outcome : SailOutcome
      ({source_len & {source_off & RlpCursor source_off source_len}}%type))
    : Prop :=
  validInputSlice bytes base len = true /\
  runRlpNodeCursor bytes node = outcome.

Definition ReviewedParentHeaderFieldsRelation {base len : Z}
    (bytes : list byte) (cursor : StatelessInputSliceFields base len)
    (fieldIndex : parent_header_field_cursor) (fields : ParentHeaderFields)
    (outcome : SailOutcome ParentHeaderFields) : Prop :=
  validInputSlice bytes base len = true /\
  0 <= parent_header_field_cursor_value fieldIndex <= 19 /\
  runParentHeaderFields bytes cursor fieldIndex fields = outcome.

Check (eq_refl : @ReferenceRlpItem = @ReviewedRlpItemRelation).
Check (eq_refl : @ReferenceRlpHeader = @ReviewedRlpHeaderRelation).
Check (eq_refl : @ReferenceRlpNode = @ReviewedRlpNodeRelation).
Check (eq_refl : @ReferenceParentHeaderFields =
                  @ReviewedParentHeaderFieldsRelation).

Print Assumptions ReferenceRlpItem.
Print Assumptions ReferenceRlpHeader.
Print Assumptions ReferenceRlpNode.
Print Assumptions ReferenceParentHeaderFields.
Ltac2 Eval exact_axioms 'ReferenceRlpItem (approved_library_axioms ()).
Ltac2 Eval exact_axioms 'ReferenceRlpHeader (approved_library_axioms ()).
Ltac2 Eval exact_axioms 'ReferenceRlpNode (approved_library_axioms ()).
Ltac2 Eval exact_axioms 'ReferenceParentHeaderFields (approved_library_axioms ()).

Definition ReviewedEncodeResultType : Type :=
  Z -> list byte -> list byte -> list byte -> candidateItem -> Prop.
Definition ReviewedRelateItemType : Type :=
  forall base len : Z, Z -> list byte -> list byte -> list byte ->
  SailItemOutcome base len -> Prop.

Check (@encodeResult : ReviewedEncodeResultType).
Check (@relateItem : ReviewedRelateItemType).
Check (@intendedValidRlpClassHeaderFits :
  forall input, intendedValidRlpClass input -> headerFits input).
Print Assumptions intendedValidRlpClassHeaderFits.
Ltac2 Eval exact_axioms 'intendedValidRlpClassHeaderFits
  (approved_library_axioms ()).

Check (@decodeItemAllowsC1B : DecodeItemArgs -> DecodeItemOutcome -> Prop).
Check (eq_refl : decodeItemAllowsC1B = decodeItemAllows C1BResult).
Check (eq_refl : knownBugs = [RlpLongLengthWrap]).

Definition ReviewedDecodeMeaningModuloKnownBugs
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : Prop :=
  decodeItemAllows C1BResult args after /\
  (decodeItemSailResult args after \/
   exists bug, List.In bug knownBugs /\ decodeItemBugApplies bug args after).

Check (@DecodeMeaningModuloKnownBugs :
  DecodeItemArgs -> DecodeItemOutcome -> Prop).
Check (eq_refl : DecodeMeaningModuloKnownBugs =
                 ReviewedDecodeMeaningModuloKnownBugs).
Check (@decodeItemWrapWitness :
  candidateDecodeItem decodeItemWrapWitnessInput =
    candidateSuccess false 9 (word64Modulus - 9) /\
  binaryWrapCase 9 (word64Modulus - 9) 0 /\
  ~ headerFits decodeItemWrapWitnessInput).
Print Assumptions decodeItemWrapWitness.
Ltac2 Eval exact_axioms 'decodeItemWrapWitness (approved_library_axioms ()).
