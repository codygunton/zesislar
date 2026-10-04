From Coq Require Import ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import Scaffolding.DecodeItemComplianceStatement.

(* Pending gate: no implementation theorem exists for this statement yet. *)
Definition ReviewedDecodeItemComplianceType : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModel returnAddress).

Check (@DecodeItemComplianceStatement : Prop).
Check (eq_refl : DecodeItemComplianceStatement =
                 ReviewedDecodeItemComplianceType).
Check (eq_refl : ReviewedDecodeItemComplianceType =
                 DecodeItemSelectedComplianceStatement).
