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
Require Import ZesuSsz.Compliance.DecodeItemFoldSuccessorWitnesses.
Require Import ZesuSsz.Automation.Switches.CanonicalAnchor.

Lemma listSuccessorNamed `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (next : byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n) ->
  ⊢ (  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args -∗
     decodeItemEntryAt800d6ac4 args prefix rest)%I.
Proof.
  intros Hguard Hdomain Hframe Hprovenance Hlookup Hbranch.
  iIntros "(Hraw & Hcont)".
  iDestruct "Hraw" as "(Hregs & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6 & Hsp & Hra & Hs0 & Hin & Hout & Hstack & %Hfacts & _)".
  destruct Hfacts as [Hlength Hfold].

  let anchor := constr:(("x13" ↦ᵣ RVal_Bits (bv_or
    (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
    (bv_zero_extend 64 next)))%I) in
  let registered := constr:(_ : ZesuCanonicalAnchor anchor
    (decodeItemEntryAt800d6ac4 args prefix rest) _) in
  let evidence := constr:(@zesu_canonical_anchor_intro _ _ _ _ registered) in
  let intro := constr:(@zesu_pure_fact_anchor_intro _ _ _ _ evidence) in
  iApply (@zesu_pure_fact_intro _ _ _ intro).
  iExists frameBytes, loaded.
  iSplit; first (iPureIntro; repeat first [assumption | split]).
  iFrame "Hregs Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hsp Hra Hs0 Hin Hout Hstack Hcont".
  iPureIntro. exact (conj (conj Hlength Hfold) I).
Qed.
Print Assumptions listSuccessorNamed.

Lemma listSuccessorExpanded `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (next : byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n) ->
  ⊢ (  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args -∗
     decodeItemEntryAt800d6ac4 args prefix rest)%I.
Proof.
  intros Hguard Hdomain Hframe Hprovenance Hlookup Hbranch.
  iIntros "(Hraw & Hcont)".
  iDestruct "Hraw" as "(Hregs & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6 & Hsp & Hra & Hs0 & Hin & Hout & Hstack & %Hfacts & _)".
  destruct Hfacts as [Hlength Hfold].
  unfold decodeItemEntryAt800d6ac4.
  let anchor := constr:(("x13" ↦ᵣ RVal_Bits (bv_or
    (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
    (bv_zero_extend 64 next)))%I) in
  let registered := constr:(_ : ZesuCanonicalAnchor anchor
    (∃ (successorN successorI successorStart : Z) (successorLength successorFrame : list byte)
       (successorLoaded : bv 64),
    ⌜successorI < successorN /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args successorFrame /\
      decodeItemFoldProvenance args true prefix rest successorN successorStart successorLength⌝ ∗
    decodeItemByteFoldListHeader args successorN successorI successorStart
      successorLength successorFrame successorLoaded ∗
    decodeItemBranchContinuation args)%I _) in
  lazymatch registered with
  | @decodeItemListSuccessorExpandedCanonical _ _ _ _ _ _ _ _ _ _ _ => idtac
  | _ => fail "The expanded companion was not selected"
  end;
  let evidence := constr:(@zesu_canonical_anchor_intro _ _ _ _ registered) in
  let intro := constr:(@zesu_pure_fact_anchor_intro _ _ _ _ evidence) in
  iApply (@zesu_pure_fact_intro _ _ _ intro).
  iExists frameBytes, loaded.
  iSplit; first (iPureIntro; repeat first [assumption | split]).
  iFrame "Hregs Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hsp Hra Hs0 Hin Hout Hstack Hcont".
  iPureIntro. exact (conj (conj Hlength Hfold) I).
Qed.
Print Assumptions listSuccessorExpanded.

Lemma listSuccessorExists `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (next : byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n) ->
  ⊢ (  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args -∗
     (∃ (successorPrefix : byte) (successorRest : list byte), decodeItemEntryAt800d6ac4 args successorPrefix successorRest))%I.
Proof.
  intros Hguard Hdomain Hframe Hprovenance Hlookup Hbranch.
  iIntros "(Hraw & Hcont)".
  iDestruct "Hraw" as "(Hregs & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6 & Hsp & Hra & Hs0 & Hin & Hout & Hstack & %Hfacts & _)".
  destruct Hfacts as [Hlength Hfold].

  zesu_canonical_anchor_if_enabled.
  iExists frameBytes, loaded.
  iSplit; first (iPureIntro; repeat first [assumption | split]).
  iFrame "Hregs Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hsp Hra Hs0 Hin Hout Hstack Hcont".
  iPureIntro. exact (conj (conj Hlength Hfold) I).
Qed.
Print Assumptions listSuccessorExists.

Lemma listSuccessorExistsExpanded `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (next : byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n) ->
  ⊢ (  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args -∗
     (∃ (successorPrefix : byte) (successorRest : list byte), decodeItemEntryAt800d6ac4 args successorPrefix successorRest))%I.
Proof.
  intros Hguard Hdomain Hframe Hprovenance Hlookup Hbranch.
  iIntros "(Hraw & Hcont)".
  iDestruct "Hraw" as "(Hregs & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6 & Hsp & Hra & Hs0 & Hin & Hout & Hstack & %Hfacts & _)".
  destruct Hfacts as [Hlength Hfold].
  unfold decodeItemEntryAt800d6ac4.
  let anchor := constr:(("x13" ↦ᵣ RVal_Bits (bv_or
    (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
    (bv_zero_extend 64 next)))%I) in
  let registered := constr:(_ : ZesuCanonicalAnchor anchor
    (∃ (successorPrefix : byte) (successorRest : list byte), (∃ (successorN successorI successorStart : Z) (successorLength successorFrame : list byte)
       (successorLoaded : bv 64),
    ⌜successorI < successorN /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args successorFrame /\
      decodeItemFoldProvenance args true successorPrefix successorRest successorN successorStart successorLength⌝ ∗
    decodeItemByteFoldListHeader args successorN successorI successorStart
      successorLength successorFrame successorLoaded ∗
    decodeItemBranchContinuation args)%I)%I _) in
  lazymatch registered with
  | @decodeItemListSuccessorExistsExpandedCanonical _ _ _ _ _ _ _ _ _ _ _ => idtac
  | _ => fail "The expanded companion was not selected"
  end;
  let evidence := constr:(@zesu_canonical_anchor_intro _ _ _ _ registered) in
  let intro := constr:(@zesu_pure_fact_anchor_intro _ _ _ _ evidence) in
  iApply (@zesu_pure_fact_intro _ _ _ intro).
  iExists frameBytes, loaded.
  iSplit; first (iPureIntro; repeat first [assumption | split]).
  iFrame "Hregs Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hsp Hra Hs0 Hin Hout Hstack Hcont".
  iPureIntro. exact (conj (conj Hlength Hfold) I).
Qed.
Print Assumptions listSuccessorExistsExpanded.

Lemma listSuccessorUnconstrainedCanonical `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  True.
Proof.
  intros.
  let anchor := constr:(("x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8) (bv_zero_extend 64 next)))%I) in
  let registered := constr:(_ : ZesuCanonicalAnchor anchor _ _) in
  lazymatch registered with
  | @decodeItemListSuccessorExistsCanonical _ _ _ _ _ _ _ _ _ _ _ => exact I
  | _ => fail "The unconstrained S68 selection changed"
  end.
Qed.
Print Assumptions listSuccessorUnconstrainedCanonical.

Lemma listSuccessorExpandedMissingFold `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  True.
Proof.
  intros.
  let anchor := constr:(("x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8) (bv_zero_extend 64 next)))%I) in
  let target := constr:((∃ (successorN successorI successorStart : Z) (successorLength successorFrame : list byte)
       (successorLoaded : bv 64),
    ⌜successorI < successorN /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args successorFrame /\
      decodeItemFoldProvenance args true prefix rest successorN successorStart successorLength⌝ ∗
    decodeItemByteFoldListHeader args successorN successorI successorStart
      successorLength successorFrame successorLoaded ∗
    decodeItemBranchContinuation args)%I) in
  let source := constr:((∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args)%I) in
  let expected := constr:(ZesuCanonicalAnchor anchor target source) in
  assert_fails (assert expected by typeclasses eauto).
  exact I.
Qed.
Print Assumptions listSuccessorExpandedMissingFold.

Lemma listSuccessorExpandedMissingProvenance `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  True.
Proof.
  intros.
  let anchor := constr:(("x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8) (bv_zero_extend 64 next)))%I) in
  let target := constr:((∃ (successorN successorI successorStart : Z) (successorLength successorFrame : list byte)
       (successorLoaded : bv 64),
    ⌜successorI < successorN /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args successorFrame /\
      decodeItemFoldProvenance args true prefix rest successorN successorStart successorLength⌝ ∗
    decodeItemByteFoldListHeader args successorN successorI successorStart
      successorLength successorFrame successorLoaded ∗
    decodeItemBranchContinuation args)%I) in
  let source := constr:((∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args)%I) in
  let expected := constr:(ZesuCanonicalAnchor anchor target source) in
  assert_fails (assert expected by typeclasses eauto).
  exact I.
Qed.
Print Assumptions listSuccessorExpandedMissingProvenance.

Lemma listSuccessorExpandedMissingLookup `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  True.
Proof.
  intros.
  let anchor := constr:(("x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8) (bv_zero_extend 64 next)))%I) in
  let target := constr:((∃ (successorN successorI successorStart : Z) (successorLength successorFrame : list byte)
       (successorLoaded : bv 64),
    ⌜successorI < successorN /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args successorFrame /\
      decodeItemFoldProvenance args true prefix rest successorN successorStart successorLength⌝ ∗
    decodeItemByteFoldListHeader args successorN successorI successorStart
      successorLength successorFrame successorLoaded ∗
    decodeItemBranchContinuation args)%I) in
  let source := constr:((∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args)%I) in
  let expected := constr:(ZesuCanonicalAnchor anchor target source) in
  assert_fails (assert expected by typeclasses eauto).
  exact I.
Qed.
Print Assumptions listSuccessorExpandedMissingLookup.

Lemma listSuccessorExpandedWrongLookup `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat i = Some next ->
  True.
Proof.
  intros.
  let anchor := constr:(("x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8) (bv_zero_extend 64 next)))%I) in
  let target := constr:((∃ (successorN successorI successorStart : Z) (successorLength successorFrame : list byte)
       (successorLoaded : bv 64),
    ⌜successorI < successorN /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args successorFrame /\
      decodeItemFoldProvenance args true prefix rest successorN successorStart successorLength⌝ ∗
    decodeItemByteFoldListHeader args successorN successorI successorStart
      successorLength successorFrame successorLoaded ∗
    decodeItemBranchContinuation args)%I) in
  let source := constr:((∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args)%I) in
  let expected := constr:(ZesuCanonicalAnchor anchor target source) in
  assert_fails (assert expected by typeclasses eauto).
  exact I.
Qed.
Print Assumptions listSuccessorExpandedWrongLookup.

Lemma listSuccessorExpandedWrongClass `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  True.
Proof.
  intros.
  let anchor := constr:(("x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8) (bv_zero_extend 64 next)))%I) in
  let target := constr:((∃ (successorN successorI successorStart : Z) (successorLength successorFrame : list byte)
       (successorLoaded : bv 64),
    ⌜successorI < successorN /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args successorFrame /\
      decodeItemFoldProvenance args true prefix rest successorN successorStart successorLength⌝ ∗
    decodeItemByteFoldListHeader args successorN successorI successorStart
      successorLength successorFrame successorLoaded ∗
    decodeItemBranchContinuation args)%I) in
  let source := constr:((∃ (frameBytes : list byte) (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes /\
      decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
      (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args)%I) in
  let expected := constr:(ZesuCanonicalAnchor anchor target source) in
  assert_fails (assert expected by typeclasses eauto).
  exact I.
Qed.
Print Assumptions listSuccessorExpandedWrongClass.
