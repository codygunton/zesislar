Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Compliance.DecodeItemJoinTransferPure.
Require Import ZesuSsz.Compliance.DecodeItemFoldExitFacts.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemListSuccessorIntroduction `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (next : byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n) ->
  ⊢ (  (listSuccessorRaw args n i payloadStart lengthBytes frameBytes next loaded) ∗ decodeItemBranchContinuation args -∗
     decodeItemEntryAt800d6ac4 args prefix rest)%I.
Proof.
  intros Hguard Hdomain Hframe Hprovenance Hlookup Hbranch.
  iIntros "(Hraw & Hcont)".
  iDestruct "Hraw" as "(Hregs & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6 & Hsp & Hra & Hs0 & Hin & Hout & Hstack & %Hfacts & _)".
  destruct Hfacts as [Hlength Hfold].
  pose proof (decodeItemByteFoldBackedgeGuard args n i payloadStart lengthBytes
    (proj2 Hdomain) Hfold Hguard Hbranch) as [Hnext _].
  pose proof Hlookup as Hnth. rewrite -decodeItemListLookupNthError in Hnth.
  pose proof (decodeItemFoldSteppedAccumulator args n i payloadStart lengthBytes next
    Hfold Hguard Hnth) as Hacc.
  pose proof (decodeItemFoldSteppedCursor args n i payloadStart lengthBytes Hfold) as Hcursor.
  iApply (decodeItemListHeaderIntro args prefix rest n (i + 1) payloadStart
    lengthBytes frameBytes loaded Hnext Hdomain Hframe Hprovenance).
  unfold decodeItemByteFoldListHeader, decodeItemByteFoldResources.
  rewrite -Hacc -Hcursor. iFrame "Hregs Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hsp Hra Hs0 Hin Hout Hstack Hcont". iPureIntro.
  unfold decodeItemByteFoldFacts in *. destruct Hfold as (Hw & Hi & Hstart & Hbytes & Hlen & Hfit).
  repeat split; try assumption; lia.
Qed.
Print Assumptions decodeItemListSuccessorIntroduction.

#[export] Instance decodeItemListSuccessorNamed `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  @ZesuPureFactAnchor Sigma (decodeItemEntryAt800d6ac4 args prefix rest)
    ("x13" ↦ᵣ RVal_Bits (bv_or
      (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
      (bv_zero_extend 64 next)))%I
    (∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (listSuccessorRaw args n i payloadStart lengthBytes frameBytes next loaded) ∗ decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%frameBytes & %loaded & %Hfacts & Hraw & Hcont)".
  destruct Hfacts as (Hguard & Hdomain & Hframe & Hprovenance & Hlookup & Hbranch).
  iApply (decodeItemListSuccessorIntroduction args prefix rest n i payloadStart
    lengthBytes frameBytes next loaded Hguard Hdomain Hframe Hprovenance Hlookup Hbranch).
  iFrame "Hraw Hcont".
Qed.

Lemma decodeItemListSuccessorNamedCanonical `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  @ZesuCanonicalAnchor Sigma ("x13" ↦ᵣ RVal_Bits (bv_or
      (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
      (bv_zero_extend 64 next)))%I
    (decodeItemEntryAt800d6ac4 args prefix rest)
    (∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (listSuccessorRaw args n i payloadStart lengthBytes frameBytes next loaded) ∗ decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuCanonicalAnchor.
  exact (decodeItemListSuccessorNamed args prefix rest n i payloadStart lengthBytes next).
Qed.

#[export] Instance decodeItemListSuccessorExists `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  @ZesuPureFactAnchor Sigma (∃ (successorPrefix : byte) (successorRest : list byte), decodeItemEntryAt800d6ac4 args successorPrefix successorRest)%I
    ("x13" ↦ᵣ RVal_Bits (bv_or
      (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
      (bv_zero_extend 64 next)))%I
    (∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (listSuccessorRaw args n i payloadStart lengthBytes frameBytes next loaded) ∗ decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%frameBytes & %loaded & %Hfacts & Hraw & Hcont)".
  destruct Hfacts as (Hguard & Hdomain & Hframe & Hprovenance & Hlookup & Hbranch).
  iExists prefix, rest.
  iApply (decodeItemListSuccessorIntroduction args prefix rest n i payloadStart
    lengthBytes frameBytes next loaded Hguard Hdomain Hframe Hprovenance Hlookup Hbranch).
  iFrame "Hraw Hcont".
Qed.

Lemma decodeItemListSuccessorExistsCanonical `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  @ZesuCanonicalAnchor Sigma ("x13" ↦ᵣ RVal_Bits (bv_or
      (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
      (bv_zero_extend 64 next)))%I
    (∃ (successorPrefix : byte) (successorRest : list byte), decodeItemEntryAt800d6ac4 args successorPrefix successorRest)%I
    (∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (listSuccessorRaw args n i payloadStart lengthBytes frameBytes next loaded) ∗ decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuCanonicalAnchor.
  exact (decodeItemListSuccessorExists args prefix rest n i payloadStart lengthBytes next).
Qed.

Print Assumptions decodeItemListSuccessorNamed.
Print Assumptions decodeItemListSuccessorExists.
Print Assumptions decodeItemListSuccessorNamedCanonical.
Print Assumptions decodeItemListSuccessorExistsCanonical.

Lemma decodeItemListSuccessorExpandedCanonical `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  @ZesuCanonicalAnchor Sigma ("x13" ↦ᵣ RVal_Bits (bv_or
      (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
      (bv_zero_extend 64 next)))%I
    (∃ (successorN successorI successorStart : Z) (successorLength successorFrame : list byte)
       (successorLoaded : bv 64),
    ⌜successorI < successorN /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args successorFrame /\
      decodeItemFoldProvenance args true prefix rest successorN successorStart successorLength⌝ ∗
    decodeItemByteFoldListHeader args successorN successorI successorStart
      successorLength successorFrame successorLoaded ∗
    decodeItemBranchContinuation args)%I
    (∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (listSuccessorRaw args n i payloadStart lengthBytes frameBytes next loaded) ∗ decodeItemBranchContinuation args)%I.
Proof.
  exact (decodeItemListSuccessorNamedCanonical args prefix rest n i payloadStart lengthBytes next).
Qed.
Print Assumptions decodeItemListSuccessorExpandedCanonical.

Lemma decodeItemListSuccessorExistsExpandedCanonical `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  @ZesuCanonicalAnchor Sigma ("x13" ↦ᵣ RVal_Bits (bv_or
      (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
      (bv_zero_extend 64 next)))%I
    (∃ (successorPrefix : byte) (successorRest : list byte), (∃ (successorN successorI successorStart : Z) (successorLength successorFrame : list byte)
       (successorLoaded : bv 64),
    ⌜successorI < successorN /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args successorFrame /\
      decodeItemFoldProvenance args true successorPrefix successorRest successorN successorStart successorLength⌝ ∗
    decodeItemByteFoldListHeader args successorN successorI successorStart
      successorLength successorFrame successorLoaded ∗
    decodeItemBranchContinuation args)%I)%I
    (∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (listSuccessorRaw args n i payloadStart lengthBytes frameBytes next loaded) ∗ decodeItemBranchContinuation args)%I.
Proof.
  exact (decodeItemListSuccessorExistsCanonical args prefix rest n i payloadStart lengthBytes next).
Qed.
Print Assumptions decodeItemListSuccessorExistsExpandedCanonical.
