Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Open Scope Z_scope.

Lemma decodeItemIntegerIndexShapeOff `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma) :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  ⊢ (continuation (Z.to_nat (1 + i)) -∗
    ∃ index : nat, ⌜Z.of_nat index =
      (payloadStart + i + 0 - decodeItemInputPointer args) `div` Z.of_N 1⌝ ∗
      continuation index)%I.
Proof.
  intros Hfold. iIntros "Hcontinuation".
  Fail zesu_pure_fact_hints_if_enabled.
  pose proof (decodeItemFoldArrayIndexWitness args n i payloadStart bytes continuation) as Hintro.
  unfold ZesuPureFactIntro in Hintro. iApply Hintro.
  iFrame. iPureIntro. exact Hfold.
Qed.

Lemma decodeItemWordIndexShapeOff `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  ⊢ (continuation (Z.to_nat (1 + i)) -∗
    ∃ index : nat, ⌜Z.of_nat index =
      (bv_unsigned (bv_add (Z_to_bv 64 (payloadStart + i)) 0) -
        decodeItemInputPointer args) `div` Z.of_N 1⌝ ∗ continuation index)%I.
Proof.
  intros Hdomain Hfold. iIntros "Hcontinuation".
  Fail zesu_pure_fact_hints_if_enabled.
  pose proof (decodeItemFoldWordArrayIndexWitness args n i payloadStart bytes continuation) as Hintro.
  unfold ZesuPureFactIntro in Hintro. iApply Hintro.
  iFrame. iSplit; iPureIntro; assumption.
Qed.

Require Import ZesuSsz.Automation.Switches.PureFactHints.

Lemma decodeItemIntegerIndexLiteralOn `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma) :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  ⊢ (continuation (Z.to_nat (1 + i)) -∗
    ∃ index : nat, ⌜Z.of_nat index =
      (payloadStart + i + 0 - decodeItemInputPointer args) `div` 1⌝ ∗ continuation index)%I.
Proof.
  intros Hfold. iIntros "Hcontinuation".
  zesu_pure_fact_hints_if_enabled. iFrame. iPureIntro. exact Hfold.
Qed.

Lemma decodeItemIntegerIndexUnreducedOn `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma) :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  ⊢ (continuation (Z.to_nat (1 + i)) -∗
    ∃ index : nat, ⌜Z.of_nat index =
      (payloadStart + i + 0 - decodeItemInputPointer args) `div` Z.of_N 1⌝ ∗ continuation index)%I.
Proof.
  intros Hfold. iIntros "Hcontinuation".
  zesu_pure_fact_hints_if_enabled. iFrame. iPureIntro. exact Hfold.
Qed.

Lemma decodeItemWordIndexLiteralOn `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  ⊢ (continuation (Z.to_nat (1 + i)) -∗
    ∃ index : nat, ⌜Z.of_nat index =
      (bv_unsigned (bv_add (Z_to_bv 64 (payloadStart + i)) 0) -
        decodeItemInputPointer args) `div` 1⌝ ∗ continuation index)%I.
Proof.
  intros Hdomain Hfold. iIntros "Hcontinuation".
  zesu_pure_fact_hints_if_enabled. iFrame. iSplit; iPureIntro; assumption.
Qed.

Lemma decodeItemWordIndexUnreducedOn `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  ⊢ (continuation (Z.to_nat (1 + i)) -∗
    ∃ index : nat, ⌜Z.of_nat index =
      (bv_unsigned (bv_add (Z_to_bv 64 (payloadStart + i)) 0) -
        decodeItemInputPointer args) `div` Z.of_N 1⌝ ∗ continuation index)%I.
Proof.
  intros Hdomain Hfold. iIntros "Hcontinuation".
  zesu_pure_fact_hints_if_enabled. iFrame. iSplit; iPureIntro; assumption.
Qed.

Lemma decodeItemWordIndexMissingDomain `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma)
    (Hfold : decodeItemByteFoldFacts args n i payloadStart bytes) : True.
Proof.
  let target := constr:((∃ index : nat, ⌜Z.of_nat index =
    (bv_unsigned (bv_add (Z_to_bv 64 (payloadStart + i)) 0) -
      decodeItemInputPointer args) `div` Z.of_N 1⌝ ∗ continuation index)%I) in
  tryif let evidence := constr:(_ : @ZesuPureFactIntro Sigma target _) in idtac
    then fail "Unexpected registration without domain" else exact I.
Qed.

Lemma decodeItemIntegerIndexUnsupportedDivisor `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma)
    (Hfold : decodeItemByteFoldFacts args n i payloadStart bytes) : True.
Proof.
  let target := constr:((∃ index : nat, ⌜Z.of_nat index =
    (payloadStart + i + 0 - decodeItemInputPointer args) `div` Z.of_N 2⌝ ∗
    continuation index)%I) in
  tryif let evidence := constr:(_ : @ZesuPureFactIntro Sigma target _) in idtac
    then fail "Unexpected registration for divisor two" else exact I.
Qed.

Lemma decodeItemWordIndexUnsupportedDivisor `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hfold : decodeItemByteFoldFacts args n i payloadStart bytes) : True.
Proof.
  let target := constr:((∃ index : nat, ⌜Z.of_nat index =
    (bv_unsigned (bv_add (Z_to_bv 64 (payloadStart + i)) 0) -
      decodeItemInputPointer args) `div` Z.of_N 2⌝ ∗ continuation index)%I) in
  tryif let evidence := constr:(_ : @ZesuPureFactIntro Sigma target _) in idtac
    then fail "Unexpected registration for divisor two" else exact I.
Qed.

Print Assumptions decodeItemIntegerIndexShapeOff.
Print Assumptions decodeItemWordIndexShapeOff.
Print Assumptions decodeItemIntegerIndexLiteralOn.
Print Assumptions decodeItemIntegerIndexUnreducedOn.
Print Assumptions decodeItemWordIndexLiteralOn.
Print Assumptions decodeItemWordIndexUnreducedOn.
Print Assumptions decodeItemWordIndexMissingDomain.
Print Assumptions decodeItemIntegerIndexUnsupportedDivisor.
Print Assumptions decodeItemWordIndexUnsupportedDivisor.
