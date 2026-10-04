From Coq Require Import ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.

(* This statement is outside the production Dune targets. *)
Definition DecodeItemComplianceStatement : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModel returnAddress).

Check (eq_refl : DecodeItemComplianceStatement =
                 DecodeItemSelectedComplianceStatement).
