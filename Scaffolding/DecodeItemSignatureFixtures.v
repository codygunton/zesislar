From Coq Require Import ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import Scaffolding.DecodeItemComplianceStatement.
Require Import Scaffolding.DecodeItemSignatureGates.

Definition fixtureExtraPremise : Prop :=
  False -> DecodeItemComplianceStatement.
Fail Check (eq_refl : fixtureExtraPremise = ReviewedDecodeItemComplianceType).

Definition fixtureChangedDomainModel (returnAddress : Z) :
    IslarisContractModel DecodeItemArgs DecodeItemOutcome :=
  let model := decodeItemSelectedModel returnAddress in
  {| islarisContractAllows := fun args after =>
       decodeItemDomainAt returnAddress (fun _ => True) args /\
       DecodeMeaningModuloKnownBugs args after;
     islarisContractStep := islarisContractStep _ _ model;
     islarisContractResources := islarisContractResources _ _ model |}.

Definition fixtureChangedDomain : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (fixtureChangedDomainModel returnAddress).
Fail Check (eq_refl : fixtureChangedDomain = ReviewedDecodeItemComplianceType).

Definition fixtureEvaluatorModel
    (evaluator : DecodeItemArgs -> DecodeItemOutcome -> Prop)
    (returnAddress : Z) :
    IslarisContractModel DecodeItemArgs DecodeItemOutcome :=
  let model := decodeItemSelectedModel returnAddress in
  {| islarisContractAllows := evaluator;
     islarisContractStep := islarisContractStep _ _ model;
     islarisContractResources := islarisContractResources _ _ model |}.

Definition fixtureHiddenEvaluator
    (evaluator : DecodeItemArgs -> DecodeItemOutcome -> Prop) : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (fixtureEvaluatorModel evaluator returnAddress).
Fail Check (@fixtureHiddenEvaluator : ReviewedDecodeItemComplianceType).
