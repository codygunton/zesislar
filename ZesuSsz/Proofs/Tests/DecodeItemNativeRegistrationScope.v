Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
From Coq Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Ltac registered_native_fact :=
  match goal with |- ?P =>
    let target := constr:(SimplAnd P True) in
    let evidence := constr:(_ : target) in exact (proj1 evidence I)
  end.

Lemma nativeRegistered_6960_5 (args : DecodeItemArgs) :
  ((Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv = Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)).
Proof. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6960_5.

Lemma nativeRegistered_6960_7 (args : DecodeItemArgs) :
  ((Z_to_bv 64 (decodeItemStackPointer args) + 18446744073709551600)%bv = Z_to_bv 64 (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes)).
Proof. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6960_7.

Lemma nativeRegistered_6a08_4 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (x13 : (bv 64)) (inputPrefix : (bv 8)) (rest : (list (bv 8))) :
  (decodeItemInputHead args inputPrefix rest) ->
  (184 ≤ bv_unsigned inputPrefix) ->
  (bv_unsigned inputPrefix ≤ 191) ->
  (bv_unsigned x13 = bv_unsigned inputPrefix) ->
  (decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) ->
  (bv_signed (bv_zero_extend 128 (bv_and (x13 + 73) 255)) >= bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args)))) ->
  ⊢ (⌜decodeItemRejectedFacts args ∧ decodeItemBeforeStorage args = decodeItemBeforeStorage args⌝%I : iProp Sigma).
Proof. intros H0 H1 H2 H3 H6 H10. iPureIntro. split; [registered_native_fact | reflexivity]. Qed.
Print Assumptions nativeRegistered_6a08_4.

Lemma nativeRegistered_6a24_3 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 183) ->
  (0 ≤ decodeItemInputPointer args) ->
  (decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus) ->
  ((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + (bv_unsigned inputPrefix - 183))) ->
  (decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 HarrayFact21 HarrayFact23 H16 H10. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6a24_3.

Lemma nativeRegistered_6a24_4 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))).
Proof. intros H5. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6a24_4.

Lemma nativeRegistered_6a24_5 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 183) ->
  (decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) ->
  (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 0) = 1073741824%bv) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 H1 H9. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6a24_5.

Lemma nativeRegistered_6a24_6 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 183) ->
  (decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) ->
  (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 0) = 1073741824%bv) ->
  ((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + i)).
Proof. intros H5 H0 H1 H9. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6a24_6.

Lemma nativeRegistered_6a24_7 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 183) ->
  (0 ≤ decodeItemInputPointer args) ->
  (decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus) ->
  ((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + (bv_unsigned inputPrefix - 183))) ->
  (decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 HarrayFact21 HarrayFact23 H17 H11. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6a24_7.

Lemma nativeRegistered_6a24_8 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))).
Proof. intros H5. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6a24_8.

Lemma nativeRegistered_6a24_11 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 183) ->
  (0 ≤ decodeItemInputPointer args) ->
  (decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus) ->
  ((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + (bv_unsigned inputPrefix - 183))) ->
  (decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 HarrayFact21 HarrayFact23 H19 H13. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6a24_11.

Lemma nativeRegistered_6a24_12 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))) ->
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 183) (bv_unsigned inputPrefix - 183) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 183)) (drop 1 (decodeItemInputBytes args)))).
Proof. intros H5. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6a24_12.

Lemma nativeRegistered_6aa8_4 `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (x13 : (bv 64)) (inputPrefix : (bv 8)) (rest : (list (bv 8))) :
  (decodeItemInputHead args inputPrefix rest) ->
  (248 ≤ bv_unsigned inputPrefix) ->
  (bv_unsigned inputPrefix ≤ 255) ->
  (bv_unsigned x13 = bv_unsigned inputPrefix) ->
  (decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) ->
  (bv_signed (bv_zero_extend 128 (bv_and (x13 + 9) 255)) >= bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args)))) ->
  ⊢ (⌜decodeItemRejectedFacts args ∧ decodeItemBeforeStorage args = decodeItemBeforeStorage args⌝%I : iProp Sigma).
Proof. intros H0 H1 H2 H3 H6 H10. iPureIntro. split; [registered_native_fact | reflexivity]. Qed.
Print Assumptions nativeRegistered_6aa8_4.

Lemma nativeRegistered_6ac4_3 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 247) ->
  (0 ≤ decodeItemInputPointer args) ->
  (decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus) ->
  ((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + (bv_unsigned inputPrefix - 247))) ->
  (decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 HarrayFact21 HarrayFact23 H16 H10. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6ac4_3.

Lemma nativeRegistered_6ac4_4 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))).
Proof. intros H5. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6ac4_4.

Lemma nativeRegistered_6ac4_5 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 247) ->
  (decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) ->
  (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 0) = 1073741824%bv) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 H1 H9. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6ac4_5.

Lemma nativeRegistered_6ac4_6 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 247) ->
  (decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) ->
  (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 0) = 1073741824%bv) ->
  ((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + i)).
Proof. intros H5 H0 H1 H9. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6ac4_6.

Lemma nativeRegistered_6ac4_7 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 247) ->
  (0 ≤ decodeItemInputPointer args) ->
  (decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus) ->
  ((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + (bv_unsigned inputPrefix - 247))) ->
  (decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 HarrayFact21 HarrayFact23 H17 H11. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6ac4_7.

Lemma nativeRegistered_6ac4_8 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))).
Proof. intros H5. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6ac4_8.

Lemma nativeRegistered_6ac4_11 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (i < bv_unsigned inputPrefix - 247) ->
  (0 ≤ decodeItemInputPointer args) ->
  (decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus) ->
  ((Z_to_bv 64 (decodeItemInputPointer args + 1 + i) + 1)%bv = Z_to_bv 64 (decodeItemInputPointer args + 1 + (bv_unsigned inputPrefix - 247))) ->
  (decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem) ->
  (bv_or (Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat i) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args))))) ≪ 8) (bv_zero_extend 64 vmem) =
 Z_to_bv 64 (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))))).
Proof. intros H5 H0 HarrayFact21 HarrayFact23 H19 H13. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6ac4_11.

Lemma nativeRegistered_6ac4_12 (args : DecodeItemArgs) (inputPrefix : (bv 8)) (i : Z) (vmem : (bv 8)) :
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) i (decodeItemInputPointer args + 1) (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))) ->
  (decodeItemByteFoldFacts args (bv_unsigned inputPrefix - 247) (bv_unsigned inputPrefix - 247) (decodeItemInputPointer args + 1)
   (take (Z.to_nat (bv_unsigned inputPrefix - 247)) (drop 1 (decodeItemInputBytes args)))).
Proof. intros H5. registered_native_fact. Qed.
Print Assumptions nativeRegistered_6ac4_12.

Lemma nativeRegistered_69a4_1 (prefix : byte) :
  128 <= bv_unsigned prefix -> bv_unsigned prefix <= 255 ->
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv ->
  129 <= bv_unsigned prefix.
Proof. intros H1 H2 H9. registered_native_fact. Qed.

Print Assumptions nativeRegistered_69a4_1.
