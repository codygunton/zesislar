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

Print Assumptions decodeItemFoldZeroAccumulator.

Lemma decodeItemFoldZeroCursor (payloadStart : Z) :
  payloadStart + 0 = payloadStart.
Proof. lia. Qed.

Print Assumptions decodeItemFoldZeroCursor.
