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

Lemma decodeItemStringSuccessorIntroduction `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (next : byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n) ->
  ⊢ ((listSuccessorRaw args n i payloadStart lengthBytes frameBytes next loaded) ∗
   decodeItemBranchContinuation args -∗
   decodeItemEntryAt800d6a24 args prefix rest)%I.
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
  iApply (decodeItemStringHeaderIntro args prefix rest n (i + 1) payloadStart
    lengthBytes frameBytes loaded Hnext Hdomain Hframe Hprovenance).
  unfold decodeItemByteFoldStringHeader, decodeItemByteFoldResources.
  rewrite -Hacc -Hcursor. iFrame "Hregs Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hsp Hra Hs0 Hin Hout Hstack Hcont". iPureIntro.
  unfold decodeItemByteFoldFacts in *. destruct Hfold as (Hw & Hi & Hstart & Hbytes & Hlen & Hfit).
  repeat split; try assumption; lia.
Qed.
Print Assumptions decodeItemStringSuccessorIntroduction.

Lemma decodeItemStringFlagUnitIntroduction `{!islaG Sigma} `{!threadG}
    (b : bv 64) (remaining : isla_trace) :
  Z.land (bv_unsigned b) 131072 = 0 ->
  @ZesuPureFactIntro Sigma
    (∃ _ : unit,
      ⌜Val_Bool (bool_decide (bv_and b 131072 = 0%bv)) = Val_Bool true⌝ ∗
      wp_asm remaining)%I
    (wp_asm remaining).
Proof.
  intros Hflag. unfold ZesuPureFactIntro.
  assert (Hbits : bv_and b 131072 = 0%bv).
  { apply bv_eq. rewrite bv_and_unsigned. change (Z.land (bv_unsigned b) 131072 = 0). exact Hflag. }
  rewrite bool_decide_true; [|exact Hbits].
  iIntros "Hremaining". iExists tt. iFrame. done.
Qed.
Print Assumptions decodeItemStringFlagUnitIntroduction.
