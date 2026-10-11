Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemDataWitnessFacts.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Coq Require Import ZArith Lia.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Compliance.DecodeItemRawOutputFacts.
Require Import ZesuSsz.Compliance.DecodeItemOutputWitnessSelections.

#[export] Instance decodeItemLiteralEntryOutputFactsIntroduction `{!islaG Sigma} `{!threadG}
 args (frameBytes : list byte) (x13 : bv 64) (prefix : byte) (rest : list byte) :
 @ZesuPureFactIntro Sigma
 (⌜ exists (pointerBytes lengthBytes : list byte) (headerLength payloadLength : Z),
 pointerBytes = bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args))) /\
 lengthBytes = bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1)) /\
 headerLength = 0 /\ payloadLength = 1 /\
 RlpDecodeItem.littleEndian pointerBytes = Z.add (decodeItemInputPointer args) headerLength /\
 RlpDecodeItem.littleEndian lengthBytes = payloadLength /\
 decodeItemAcceptedFacts args false headerLength payloadLength /\
 decodeItemInputHead args prefix rest /\ decodeItemSavedFrameFacts args frameBytes⌝)%I
 (decodeItemEntryAt800d697c args frameBytes x13 prefix rest)%I.
Proof.
unfold ZesuPureFactIntro.
unfold decodeItemEntryAt800d697c.
iIntros "Hentry".
iDestruct "Hentry" as (x14 x15 x16) "(%Hfacts & H13 & H14 & H15 & H16 & Hbase)".
iEval (unfold decodeItemBranchBase) in "Hbase".
iDestruct "Hbase" as "(Hregs & H10 & H11 & H12 & H2 & H1 & H8 & Hin & Hout & Hstack & %Hbase & Hcont & _)".
iPureIntro.
destruct Hfacts as (Hhead & Hclass & Hregister & Haccepted & Hsigned).
destruct Hbase as [Hframe Hdomain].
destruct (proj2 Hdomain) as (Hinput & Hbefore & Hp & Hl & Hnowrap & Hlayout).
pose proof (decodeItemRawInputPointer args Hp Hl Hnowrap) as Hpointer.
exists (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)))),
 (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 1))), 0, 1.
rewrite !decodeItemStoredWordValue.
assert (Hone : bv_unsigned (Z_to_bv 64 1) = 1) by reflexivity.
exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj Hpointer (conj Hone (conj Haccepted (conj Hhead Hframe)))))))).
Qed.

Print Assumptions decodeItemLiteralEntryOutputFactsIntroduction.

#[export] Instance decodeItemShortStringEntryOutputFactsIntroduction `{!islaG Sigma} `{!threadG}
 args (frameBytes : list byte) (x13 : bv 64) (prefix : byte) (rest : list byte) :
 @ZesuPureFactIntro Sigma
 (⌜ exists (pointerBytes lengthBytes : list byte) (headerLength payloadLength : Z),
 pointerBytes = bv_to_little_endian 8 8 (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1)) /\
 lengthBytes = bv_to_little_endian 8 8 (bv_unsigned x13) /\
 headerLength = 1 /\ payloadLength = Z.sub (bv_unsigned prefix) 128 /\
 RlpDecodeItem.littleEndian pointerBytes = Z.add (decodeItemInputPointer args) headerLength /\
 RlpDecodeItem.littleEndian lengthBytes = payloadLength /\
 decodeItemAcceptedFacts args false headerLength payloadLength /\
 decodeItemInputHead args prefix rest /\ decodeItemSavedFrameFacts args frameBytes⌝)%I
 (decodeItemEntryAt800d69e8 args frameBytes x13 prefix rest)%I.
Proof.
unfold ZesuPureFactIntro.
unfold decodeItemEntryAt800d69e8.
iIntros "Hentry".
iDestruct "Hentry" as (x15 x16) "(%Hfacts & H13 & H14 & H15 & H16 & Hbase)".
iEval (unfold decodeItemBranchBase) in "Hbase".
iDestruct "Hbase" as "(Hregs & H10 & H11 & H12 & H2 & H1 & H8 & Hin & Hout & Hstack & %Hbase & Hcont & _)".
iPureIntro.
destruct Hfacts as (Hhead & Hclass & Hvalue & Haccepted & Hguard).
destruct Hbase as [Hframe Hdomain].
destruct Hclass as [Hlow Hhigh].
destruct (proj2 Hdomain) as (Hinput & Hbefore & Hp & Hl & Hnowrap & Hlayout).
pose proof (decodeItemRawInputSuccessor args prefix rest Hhead Hinput Hp Hnowrap) as Hpointer.
exists (bv_to_little_endian 8 8 (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1))),
 (bv_to_little_endian 8 8 (bv_unsigned x13)), 1, (bv_unsigned prefix - 128).
rewrite !decodeItemStoredWordValue.
exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj Hpointer (conj Hvalue (conj Haccepted (conj Hhead Hframe)))))))).
Qed.

Print Assumptions decodeItemShortStringEntryOutputFactsIntroduction.

#[export] Instance decodeItemCanonicalEntryFrameFactsIntroduction `{!islaG Sigma} `{!threadG}
 returnAddress args :
 @ZesuPureFactIntro Sigma
 (⌜decodeItemSavedFrameFacts args
 (List.app (bv_to_little_endian 8 8 (bv_unsigned (decodeItemSavedFramePointer args)))
  (bv_to_little_endian 8 8 (bv_unsigned (Z_to_bv 64 (decodeItemReturnAddress args)))))⌝)%I
 (decodeItemEntryAt800d6960 returnAddress args)%I.
Proof.
unfold ZesuPureFactIntro.
unfold decodeItemEntryAt800d6960, decodeItemEntryResources.
iIntros "Hentry".
iDestruct "Hentry" as "(Hentry & Hcont)".
iDestruct "Hentry" as (a3 a4 a5 a6) "(Hregs & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %Hdomain & _)".
iPureIntro.
exact (decodeItemSavedFrameFacts_machine_words args (proj2 Hdomain)).
Qed.

Print Assumptions decodeItemCanonicalEntryFrameFactsIntroduction.
