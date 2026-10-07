Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Coq Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Lemma foldExitRegistrationOff args n i payloadStart bytes next :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  0 <= decodeItemInputPointer args ->
  decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv = Z_to_bv 64 (payloadStart + n) ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next -> True.
Proof.
  intros Hfold Hguard Hp Hnowrap Heq Hlookup.
  let target := constr:(SimplAnd
    (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
      (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat n) bytes))) True) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Require Import ZesuSsz.Compliance.DecodeItemFoldExitFacts.
Require Import ZesuSsz.Compliance.DecodeItemCompletedFoldFacts.

Ltac fold_exit_registered :=
  match goal with |- ?P =>
    let target := constr:(SimplAnd P True) in
    let evidence := constr:(_ : target) in exact (proj1 evidence I)
  end.

Lemma foldNativeGoal3 (args : DecodeItemArgs) (inputPrefix : byte) (i : Z) (vmem : byte) :
((decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ->
((i < bv_unsigned inputPrefix - 247)) ->
((0 ≤ decodeItemInputPointer args)) ->
((decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus)) ->
(((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + (bv_unsigned inputPrefix - 247)))) ->
((decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem)) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 HarrayFact21 HarrayFact23 H16 H10. fold_exit_registered. Qed.

Lemma foldNativeGoal4 (args : DecodeItemArgs) (inputPrefix : byte) (i : Z) (vmem : byte) :
((decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ->
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))).
Proof. intros H5. fold_exit_registered. Qed.

Lemma foldNativeGoal5 (args : DecodeItemArgs) (inputPrefix : byte) (i : Z) (vmem : byte) :
((decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ->
((i < bv_unsigned inputPrefix - 247)) ->
((decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)) ->
((bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 0) = 1073741824%bv)) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 H1 H9. fold_exit_registered. Qed.

Lemma foldNativeGoal6 (args : DecodeItemArgs) (inputPrefix : byte) (i : Z) (vmem : byte) :
((decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ->
((i < bv_unsigned inputPrefix - 247)) ->
((decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)) ->
((bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 0) = 1073741824%bv)) ->
  ((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + i)).
Proof. intros H5 H0 H1 H9. fold_exit_registered. Qed.

Lemma foldNativeGoal7 (args : DecodeItemArgs) (inputPrefix : byte) (i : Z) (vmem : byte) :
((decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ->
((i < bv_unsigned inputPrefix - 247)) ->
((0 ≤ decodeItemInputPointer args)) ->
((decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus)) ->
(((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + (bv_unsigned inputPrefix - 247)))) ->
((decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem)) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 HarrayFact21 HarrayFact23 H17 H11. fold_exit_registered. Qed.

Lemma foldNativeGoal8 (args : DecodeItemArgs) (inputPrefix : byte) (i : Z) (vmem : byte) :
((decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ->
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))).
Proof. intros H5. fold_exit_registered. Qed.

Lemma foldNativeGoal11 (args : DecodeItemArgs) (inputPrefix : byte) (i : Z) (vmem : byte) :
((decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ->
((i < bv_unsigned inputPrefix - 247)) ->
((0 ≤ decodeItemInputPointer args)) ->
((decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus)) ->
(((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + (bv_unsigned inputPrefix - 247)))) ->
((decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem)) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 HarrayFact21 HarrayFact23 H19 H13. fold_exit_registered. Qed.

Lemma foldNativeGoal12 (args : DecodeItemArgs) (inputPrefix : byte) (i : Z) (vmem : byte) :
((decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ->
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))).
Proof. intros H5. fold_exit_registered. Qed.

Lemma foldExitMissingLookup args n i payloadStart bytes (next : byte) :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  0 <= decodeItemInputPointer args ->
  decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv = Z_to_bv 64 (payloadStart + n) -> True.
Proof.
  intros Hfold Hguard Hp Hnowrap Heq.
  let target := constr:(SimplAnd
    (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
      (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat n) bytes))) True) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma foldMetadataMissingDomain args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  bv_zero_extend 128 ((Z_to_bv 64 (payloadStart + i) + 0)%bv) = 1073741824%bv -> True.
Proof.
  intros Hfold Hguard Hmetadata.
  assert_fails (assert (SimplAnd False True) by typeclasses eauto).
  exact I.
Qed.

Lemma foldMetadataContradictionOn args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  bv_zero_extend 128 ((Z_to_bv 64 (payloadStart + i) + 0)%bv) = 1073741824%bv -> False.
Proof. intros. fold_exit_registered. Qed.

Print Assumptions foldExitRegistrationOff.
Print Assumptions foldNativeGoal3.
Print Assumptions foldNativeGoal4.
Print Assumptions foldNativeGoal5.
Print Assumptions foldNativeGoal6.
Print Assumptions foldNativeGoal7.
Print Assumptions foldNativeGoal8.
Print Assumptions foldNativeGoal11.
Print Assumptions foldNativeGoal12.
Print Assumptions foldExitMissingLookup.
Print Assumptions foldMetadataMissingDomain.
Print Assumptions foldMetadataContradictionOn.
