From Coq Require Import Lists.List ZArith.ZArith.
Require Import EvmSail.evm_decoder_types.
Require Import ZesislarProofs.Compliance.KnownBugs.
Require Import ZesislarProofs.Compliance.EvmSailAdapter.
Require Import ZesislarProofs.Contracts.Coarse.

Import ListNotations.

Definition ByteString := list Z.
Definition maxInputBytes : nat := 64 * 1024 * 1024.
Definition InputWithinBound (input : ByteString) : Prop :=
  Nat.le (length input) maxInputBytes.

Inductive DecodeOutcome : Type :=
| DecodeSuccess (value : StatelessInput)
| DecodeFailure.

(** The endpoint relation remains abstract until the machine proof connects
    the pinned ELF to generated Isla traces. *)
Record EndpointSemantics : Type := {
  endpointRuns : ByteString -> DecodeOutcome -> Prop
}.

Record ReferenceSemantics : Type := {
  referenceRuns : ByteString -> DecodeOutcome -> Prop
}.

(** This constructor connects the abstract outcome relation to EVM-Sail. *)
Definition EvmSailReference
    (runner : DecoderEvaluator)
    (model : DecoderModel)
    (inputRef : ByteString -> option StatelessInputRef) : ReferenceSemantics :=
  {| referenceRuns := fun bytes outcome =>
       exists ref, inputRef bytes = Some ref /\
         match outcome with
         | DecodeSuccess decoded => ReferenceDecodes runner model bytes ref decoded
         | DecodeFailure => ReferenceRejects runner model bytes ref
         end |}.

Definition OutcomeRelation := DecodeOutcome -> DecodeOutcome -> Prop.
Definition BugApplies := KnownBug -> ByteString -> DecodeOutcome -> Prop.

Definition OutcomeEquivalentModulo
    (applies : BugApplies)
    (equivalent : OutcomeRelation)
    (input : ByteString)
    (actual expected : DecodeOutcome) : Prop :=
  equivalent actual expected \/
  exists bug, In bug knownBugs /\ applies bug input actual.

(** This proposition states compliance modulo only the fixed bug list. *)
Definition ComplianceModuloKnownBugs
    (endpoint : EndpointSemantics)
    (reference : ReferenceSemantics)
    (applies : BugApplies)
    (equivalent : OutcomeRelation) : Prop :=
  forall input actual expected,
    InputWithinBound input ->
    endpointRuns endpoint input actual ->
    referenceRuns reference input expected ->
    OutcomeEquivalentModulo applies equivalent input actual expected.

Definition AvoidKnownBugs
    (applies : BugApplies) (input : ByteString) : Prop :=
  forall bug actual, In bug knownBugs -> ~ applies bug input actual.

(** This proposition states exact compliance for one selected input. *)
Definition ComplianceForInput
    (endpoint : EndpointSemantics)
    (reference : ReferenceSemantics)
    (equivalent : OutcomeRelation)
    (input : ByteString) : Prop :=
  InputWithinBound input /\
  forall actual expected,
    endpointRuns endpoint input actual ->
    referenceRuns reference input expected ->
    equivalent actual expected.

(** Later machine proofs must discharge these six assumptions. *)
Definition CoarseContractAssumptions
    (readInput allocatorGet sszDecode writeSuccess writeFailure zkvmExit :
      CoarseContract) : Prop :=
  contractImplements readInput /\
  contractImplements allocatorGet /\
  contractImplements sszDecode /\
  contractImplements writeSuccess /\
  contractImplements writeFailure /\
  contractImplements zkvmExit.

(** This target keeps the intended conditional proof strategy explicit. *)
Definition ConditionalCompliance
    (assumptions : Prop)
    (endpoint : EndpointSemantics)
    (reference : ReferenceSemantics)
    (applies : BugApplies)
    (equivalent : OutcomeRelation) : Prop :=
  assumptions ->
  ComplianceModuloKnownBugs endpoint reference applies equivalent.

Definition ConditionalExactCompliance
    (assumptions : Prop)
    (endpoint : EndpointSemantics)
    (reference : ReferenceSemantics)
    (applies : BugApplies)
  (equivalent : OutcomeRelation)
  (input : ByteString) : Prop :=
  assumptions -> InputWithinBound input -> AvoidKnownBugs applies input ->
  ComplianceForInput endpoint reference equivalent input.

(** This is the main statement that later proof work must establish. *)
Definition MainComplianceStatement
    (readInput allocatorGet sszDecode writeSuccess writeFailure zkvmExit :
      CoarseContract)
    (endpoint : EndpointSemantics)
    (reference : ReferenceSemantics)
    (applies : BugApplies)
    (equivalent : OutcomeRelation) : Prop :=
  ConditionalCompliance
    (CoarseContractAssumptions readInput allocatorGet sszDecode
      writeSuccess writeFailure zkvmExit)
    endpoint reference applies equivalent.
