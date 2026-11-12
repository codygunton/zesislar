Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
(* The production theorem rests on the 24 generated block proofs. *)
Require Export ZesuSsz.Compliance.DecodeItemComplianceGenerated.
Require Import ZesuSsz.Compliance.DecodeItemCompositionalBridge.
Open Scope Z_scope.

Definition ReviewedDecodeItemComplianceType : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModel returnAddress).

Lemma decodeItemSelectedCompliance
 :
  ReviewedDecodeItemComplianceType.
Proof.
  unfold ReviewedDecodeItemComplianceType.
  intros returnAddress.
  apply decodeItemRegisterComplianceWeakens.
  apply decodeItemGeneratedComplianceRegisters.
Qed.
