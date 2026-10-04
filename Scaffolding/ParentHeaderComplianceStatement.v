From Coq Require Import ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Contracts.ParentHeaderSelected.

(* These statements remain outside the production Dune targets. *)
Definition NextUint64ComplianceStatement : Prop :=
  forall returnAddress,
    IslarisContractCorrect nextUint64Entry returnAddress
      (nextUint64SelectedModel returnAddress).

Definition ParentHeaderComplianceStatement : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeParentHeaderEntry returnAddress
      (parentHeaderSelectedModel returnAddress).

Check (eq_refl : NextUint64ComplianceStatement =
                 NextUint64SelectedCorrect).
Check (eq_refl : ParentHeaderComplianceStatement =
                 ParentHeaderSelectedCorrect).
