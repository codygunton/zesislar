Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemBigEndianNonnegativePure (bytes : list byte) :
  0 <= bigEndian bytes.
Proof. exact (proj1 (decodeItemLengthBytesValueRange bytes)). Qed.

Lemma decodeItemCompletedFoldHeaderEndBound args n payloadStart bytes :
  decodeItemC1BDomain args ->
  decodeItemByteFoldFacts args n n payloadStart bytes ->
  0 <= decodeItemInputPointer args + 1 + n < word64Modulus.
Proof.
  intros Hdomain (Hwidth & Hi & Hstart & Hbytes & Hlength & Hfits).
  destruct Hdomain as (Hinput & Hstorage & Hlayout).
  destruct Hlayout as (Hpointer & HlengthRange & Hnowrap & _).
  lia.
Qed.

#[export] Hint Extern 1
  (SimplAnd (0 <= bigEndian ?bytes) True) =>
  unfold SimplAnd; split;
  [intros _; exact (decodeItemBigEndianNonnegativePure bytes) | intros _; exact I]
  : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (0 <= bigEndian ?bytes < word64Modulus) True) =>
  match goal with
  | Hfold : decodeItemByteFoldFacts ?args ?n ?n ?base bytes |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemCompletedFoldValueBounds args n base bytes Hfold)
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (0 <= decodeItemInputPointer ?args + 1 + ?n < word64Modulus) True) =>
  match goal with
  | Hdomain : decodeItemC1BDomain args,
    Hfold : decodeItemByteFoldFacts args n n ?base ?bytes |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemCompletedFoldHeaderEndBound args n base bytes Hdomain Hfold)
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (bigEndian ?bytes < word64Modulus) True) =>
  match goal with
  | Hfold : decodeItemByteFoldFacts ?args ?n ?n ?base bytes |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (proj2 (decodeItemCompletedFoldValueBounds args n base bytes Hfold))
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (decodeItemInputPointer ?args + 1 + ?n < word64Modulus) True) =>
  match goal with
  | Hdomain : decodeItemC1BDomain args,
    Hfold : decodeItemByteFoldFacts args n n ?base ?bytes |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (proj2 (decodeItemCompletedFoldHeaderEndBound args n base bytes Hdomain Hfold))
    | intros _; exact I]
  end : typeclass_instances.
