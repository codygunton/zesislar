Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Ltac completed_fold_contradiction_registered :=
  match goal with |- ?P =>
    let evidence := constr:(_ : SimplAnd P True) in
    exact (proj1 evidence I)
  end.

Lemma completedFoldAdapterGoal1 (args : DecodeItemArgs) (inputPrefix : bv 8) :
  (RlpDecodeItemByteFold.decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 183) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))) = false) ->
  (¬ (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) <
    bv_signed
      (bv_zero_extend 128
         (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))))) +
          Z_to_bv 64 (bv_unsigned inputPrefix - 183 + 1))))%Z) ->
  False.
Proof. intros H5 H0 H8. completed_fold_contradiction_registered. Qed.

Lemma completedFoldAdapterGoal2 (args : DecodeItemArgs) (inputPrefix : bv 8) :
  (RlpDecodeItemByteFold.decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 183) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))) = false) ->
  (¬ (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) <
    bv_signed
      (bv_zero_extend 128
         (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))))) +
          Z_to_bv 64 (bv_unsigned inputPrefix - 183 + 1))))%Z) ->
  False.
Proof. intros H5 H0 H8. completed_fold_contradiction_registered. Qed.

Lemma completedFoldAdapterGoal3 (args : DecodeItemArgs) (inputPrefix : bv 8) :
  (RlpDecodeItemByteFold.decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 183) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))) = false) ->
  (¬ (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) <
    bv_signed
      (bv_zero_extend 128
         (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))))) +
          Z_to_bv 64 (bv_unsigned inputPrefix - 183 + 1))))%Z) ->
  False.
Proof. intros H5 H0 H8. completed_fold_contradiction_registered. Qed.

Lemma completedFoldAdapterGoal4 (args : DecodeItemArgs) (inputPrefix : bv 8) :
  (RlpDecodeItemByteFold.decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 247) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))) = false) ->
  (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) >=
 bv_signed
   (bv_zero_extend 128
      (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) +
       Z_to_bv 64 (bv_unsigned inputPrefix - 247 + 1))))%Z ->
  False.
Proof. intros H5 H0 H8. completed_fold_contradiction_registered. Qed.

Lemma completedFoldAdapterGoal5 (args : DecodeItemArgs) (inputPrefix : bv 8) :
  (RlpDecodeItemByteFold.decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 247) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))) = false) ->
  (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) >=
 bv_signed
   (bv_zero_extend 128
      (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) +
       Z_to_bv 64 (bv_unsigned inputPrefix - 247 + 1))))%Z ->
  False.
Proof. intros H5 H0 H8. completed_fold_contradiction_registered. Qed.

Lemma completedFoldAdapterGoal6 (args : DecodeItemArgs) (inputPrefix : bv 8) :
  (RlpDecodeItemByteFold.decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 247) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))) = false) ->
  (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) >=
 bv_signed
   (bv_zero_extend 128
      (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) +
       Z_to_bv 64 (bv_unsigned inputPrefix - 247 + 1))))%Z ->
  False.
Proof. intros H5 H0 H8. completed_fold_contradiction_registered. Qed.

Lemma completedFoldMissingPremise1 (args : DecodeItemArgs) (inputPrefix : bv 8) :
  (RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 183) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))) = false) ->
  (¬ (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) <
    bv_signed
      (bv_zero_extend 128
         (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))))) +
          Z_to_bv 64 (bv_unsigned inputPrefix - 183 + 1))))%Z) ->
  True.
Proof.
  intros H0 H8.
  let target := constr:(SimplAnd False True) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma completedFoldMissingPremise2 (args : DecodeItemArgs) (inputPrefix : bv 8) :
  (RlpDecodeItemByteFold.decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (¬ (bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))) <
    bv_signed
      (bv_zero_extend 128
         (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))))) +
          Z_to_bv 64 (bv_unsigned inputPrefix - 183 + 1))))%Z) ->
  True.
Proof.
  intros H5 H8.
  let target := constr:(SimplAnd False True) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma completedFoldMissingPremise3 (args : DecodeItemArgs) (inputPrefix : bv 8) :
  (RlpDecodeItemByteFold.decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (RlpDecodeItemByteFoldBlocks.decodeItemFoldLengthFits args (bv_unsigned inputPrefix - 183) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))) = false) ->
  True.
Proof.
  intros H5 H0.
  let target := constr:(SimplAnd False True) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

