Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Open Scope Z_scope.

Lemma decodeItemInitializationCursor args isList prefix rest n payloadStart bytes :
  decodeItemFoldProvenance args isList prefix rest n payloadStart bytes ->
  (Z_to_bv 64 (decodeItemInputPointer args) + (Z_to_bv 64 n + 1))%bv =
    Z_to_bv 64 (payloadStart + n).
Proof.
  intros Hprovenance.
  assert (Hstart : payloadStart = decodeItemInputPointer args + 1) by
    (unfold decodeItemFoldProvenance in Hprovenance; tauto).
  rewrite Hstart. bv_solve.
Qed.

Lemma decodeItemInitializationStartCursor args isList prefix rest n payloadStart bytes :
  decodeItemFoldProvenance args isList prefix rest n payloadStart bytes ->
  (Z_to_bv 64 (decodeItemInputPointer args) + 1)%bv = Z_to_bv 64 (payloadStart + 0).
Proof.
  intros Hprovenance.
  assert (Hstart : payloadStart = decodeItemInputPointer args + 1) by
    (unfold decodeItemFoldProvenance in Hprovenance; tauto).
  rewrite Hstart. bv_solve.
Qed.

Print Assumptions decodeItemInitializationCursor.
Print Assumptions decodeItemInitializationStartCursor.
