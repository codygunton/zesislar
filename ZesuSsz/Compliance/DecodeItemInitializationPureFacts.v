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

#[export] Hint Extern 1 (SimplAnd (0 < ?n) True) =>
  match goal with
  | Hfold : decodeItemByteFoldFacts ?args n 0 ?payloadStart ?bytes |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemByteFoldFirstGuard args n payloadStart bytes Hfold)
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd ((Z_to_bv 64 (decodeItemInputPointer ?args) + (Z_to_bv 64 ?n + 1))%bv =
    Z_to_bv 64 (?payloadStart + ?n)) True) =>
  match goal with
  | Hprovenance : decodeItemFoldProvenance args ?isList ?prefix ?rest n payloadStart ?bytes |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemInitializationCursor args isList prefix rest n payloadStart bytes Hprovenance)
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd ((Z_to_bv 64 (decodeItemInputPointer ?args) + 1)%bv =
    Z_to_bv 64 (?payloadStart + 0)) True) =>
  match goal with
  | Hprovenance : decodeItemFoldProvenance args ?isList ?prefix ?rest ?n payloadStart ?bytes |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemInitializationStartCursor args isList prefix rest n payloadStart bytes Hprovenance)
    | intros _; exact I]
  end : typeclass_instances.

Print Assumptions decodeItemInitializationCursor.
Print Assumptions decodeItemInitializationStartCursor.
