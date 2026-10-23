Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Compliance.DecodeItemCompletedFoldFacts.
Require Import ZesuSsz.Generated.DecodeItem.Registrations.
Open Scope Z_scope.

Lemma decodeItemCompletedFoldActivation args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  SimplAnd (decodeItemByteFoldFacts args n n payloadStart bytes) True.
Proof. intros Hfold. typeclasses eauto. Qed.

Lemma decodeItemCompletedListFoldResidualActivation args (prefix : byte) i :
  decodeItemByteFoldFacts args (bv_unsigned prefix - 247) i
    (decodeItemInputPointer args + 1)
    (take (Z.to_nat (bv_unsigned prefix - 247)) (drop 1 (decodeItemInputBytes args))) ->
  SimplAnd
    (decodeItemByteFoldFacts args (bv_unsigned prefix - 247) (bv_unsigned prefix - 247)
      (decodeItemInputPointer args + 1)
      (take (Z.to_nat (bv_unsigned prefix - 247)) (drop 1 (decodeItemInputBytes args)))) True.
Proof. intros Hfold. typeclasses eauto. Qed.

Print Assumptions decodeItemCompletedFoldActivation.
Print Assumptions decodeItemCompletedListFoldResidualActivation.
