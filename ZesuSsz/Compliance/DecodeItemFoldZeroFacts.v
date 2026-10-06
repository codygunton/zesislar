Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Open Scope Z_scope.

Lemma decodeItemFoldZeroAccumulator (lengthBytes : list byte) :
  (0%bv : bv 64) =
    Z_to_bv 64 (bigEndian (take (Z.to_nat 0) lengthBytes)).
Proof.
  change (0%bv = Z_to_bv 64 (bigEndian ([] : list byte))).
  unfold bigEndian. simpl. bv_solve.
Qed.

#[export] Instance decodeItemFoldZeroAccumulatorHint (lengthBytes : list byte) :
  SimplAnd ((0%bv : bv 64) =
    Z_to_bv 64 (bigEndian (take (Z.to_nat 0) lengthBytes))) True.
Proof.
  unfold SimplAnd. split;
    [intros _; apply decodeItemFoldZeroAccumulator | intros _; exact I].
Qed.

Print Assumptions decodeItemFoldZeroAccumulator.
Print Assumptions decodeItemFoldZeroAccumulatorHint.

Lemma decodeItemFoldZeroCursor (payloadStart : Z) :
  payloadStart + 0 = payloadStart.
Proof. lia. Qed.

#[export] Instance decodeItemFoldZeroCursorHint (payloadStart : Z) :
  SimplAnd (payloadStart + 0 = payloadStart) True.
Proof.
  unfold SimplAnd. split;
    [intros _; apply decodeItemFoldZeroCursor | intros _; exact I].
Qed.

Print Assumptions decodeItemFoldZeroCursor.
Print Assumptions decodeItemFoldZeroCursorHint.
