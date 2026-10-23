Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
Require Import ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
Require Import ZesuSsz.Generated.DecodeItem.Registrations.
Require Import ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Compliance.DecodeItemFoldInitializationWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Require Import ZesuSsz.Automation.Switches.PureFactHints.
Require Import ZesuSsz.Compliance.DecodeItemCanonicalAnchors.

(* These registrations belong only to the generic mechanism tests. *)
#[local] Hint Extern 1
  (@ZesuCanonicalAnchor ?Sigma
    (decodeItemByteFoldStringHeader ?args ?n 0 ?payloadStart ?bytes ?frameBytes ?loaded) _ _) =>
  match goal with
  | Hprovenance : decodeItemFoldProvenance args false ?prefix ?rest n payloadStart bytes |- _ =>
    exact (@decodeItemStringInitializationAnchorCanonical Sigma _ _ args prefix rest n payloadStart bytes frameBytes loaded)
  end : typeclass_instances.

#[local] Hint Extern 1
  (@ZesuCanonicalAnchor ?Sigma
    (decodeItemByteFoldListHeader ?args ?n 0 ?payloadStart ?bytes ?frameBytes ?loaded) _ _) =>
  match goal with
  | Hprovenance : decodeItemFoldProvenance args true ?prefix ?rest n payloadStart bytes |- _ =>
    exact (@decodeItemListInitializationAnchorCanonical Sigma _ _ args prefix rest n payloadStart bytes frameBytes loaded)
  end : typeclass_instances.

#[local] Hint Extern 1
  (@ZesuCanonicalAnchor ?Sigma
    (decodeItemFoldInitResources ?args ?n ?payloadStart ?bytes ?frameBytes ?oldAcc ?oldCursor ?loaded) _ _) =>
  first [
    match goal with
    | Hprovenance : decodeItemFoldProvenance args false ?prefix ?rest n payloadStart bytes |- _ =>
      exact (@decodeItemStringSliceWitnessCanonical Sigma _ _ args prefix rest frameBytes oldAcc oldCursor loaded)
    end
  | match goal with
    | Hprovenance : decodeItemFoldProvenance args true ?prefix ?rest n payloadStart bytes |- _ =>
      exact (@decodeItemListSliceWitnessCanonical Sigma _ _ args prefix rest frameBytes oldAcc oldCursor loaded)
    end ] : typeclass_instances.

#[local] Hint Extern 1
  (@ZesuCanonicalAnchor ?Sigma
    (decodeItemFoldCheckedResources ?args ?n ?payloadStart ?bytes ?frameBytes ?loaded) _ _) =>
  first [
    match goal with
    | Hprovenance : decodeItemFoldProvenance args false ?prefix ?rest n payloadStart bytes |- _ =>
      exact (@decodeItemStringReturnLengthWitnessCanonical Sigma _ _ args prefix rest n payloadStart bytes frameBytes loaded)
    end
  | match goal with
    | Hprovenance : decodeItemFoldProvenance args true ?prefix ?rest n payloadStart bytes |- _ =>
      exact (@decodeItemListReturnLengthWitnessCanonical Sigma _ _ args prefix rest n payloadStart bytes frameBytes loaded)
    end ] : typeclass_instances.

Lemma decodeItemStringInitializationAnchorCanonicalOff
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  ⊢ ((⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I -∗ (decodeItemEntryAt800d6a24 args prefix rest))%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfold & %Hdomain & %Hframe & %Hprovenance & Hanchor & Hcont)".
Fail zesu_canonical_anchor_if_enabled.
pose proof (decodeItemStringInitializationAnchorCanonical args prefix rest n payloadStart lengthBytes frameBytes loaded) as Hintro.
unfold ZesuCanonicalAnchor, ZesuPureFactAnchor, ZesuPureFactIntro in Hintro.
iApply Hintro. iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemListInitializationAnchorCanonicalOff
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  ⊢ ((⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I -∗ (decodeItemEntryAt800d6ac4 args prefix rest))%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfold & %Hdomain & %Hframe & %Hprovenance & Hanchor & Hcont)".
Fail zesu_canonical_anchor_if_enabled.
pose proof (decodeItemListInitializationAnchorCanonical args prefix rest n payloadStart lengthBytes frameBytes loaded) as Hintro.
unfold ZesuCanonicalAnchor, ZesuPureFactAnchor, ZesuPureFactIntro in Hintro.
iApply Hintro. iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemStringSliceWitnessCanonicalOff
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) :
  ⊢ ((⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 183)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I -∗ (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I)%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfacts & Hanchor & Hcont)".
pose proof Hfacts as (_ & Hprovenance & _).
Fail zesu_canonical_anchor_if_enabled.
pose proof (decodeItemStringSliceWitnessCanonical args prefix rest frameBytes oldAcc oldCursor loaded) as Hintro.
unfold ZesuCanonicalAnchor, ZesuPureFactAnchor, ZesuPureFactIntro in Hintro.
iApply Hintro. iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemListSliceWitnessCanonicalOff
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) :
  ⊢ ((⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 247)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I -∗ (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I)%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfacts & Hanchor & Hcont)".
pose proof Hfacts as (_ & Hprovenance & _).
Fail zesu_canonical_anchor_if_enabled.
pose proof (decodeItemListSliceWitnessCanonical args prefix rest frameBytes oldAcc oldCursor loaded) as Hintro.
unfold ZesuCanonicalAnchor, ZesuPureFactAnchor, ZesuPureFactIntro in Hintro.
iApply Hintro. iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemStringReturnLengthWitnessCanonicalOff
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n payloadStart : Z) (bytes frameBytes : list byte) (loaded : bv 64) :
  ⊢ ((⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I -∗ (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength)%I)%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfacts & Hanchor & Hcont)".
pose proof Hfacts as (_ & _ & Hprovenance & _).
Fail zesu_canonical_anchor_if_enabled.
pose proof (decodeItemStringReturnLengthWitnessCanonical args prefix rest n payloadStart bytes frameBytes loaded) as Hintro.
unfold ZesuCanonicalAnchor, ZesuPureFactAnchor, ZesuPureFactIntro in Hintro.
iApply Hintro. iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemListReturnLengthWitnessCanonicalOff
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n payloadStart : Z) (bytes frameBytes : list byte) (loaded : bv 64) :
  ⊢ ((⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I -∗ (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength)%I)%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfacts & Hanchor & Hcont)".
pose proof Hfacts as (_ & _ & Hprovenance & _).
Fail zesu_canonical_anchor_if_enabled.
pose proof (decodeItemListReturnLengthWitnessCanonical args prefix rest n payloadStart bytes frameBytes loaded) as Hintro.
unfold ZesuCanonicalAnchor, ZesuPureFactAnchor, ZesuPureFactIntro in Hintro.
iApply Hintro. iFrame "Hanchor Hcont". iFrame "%".
Qed.

Require Import ZesuSsz.Automation.Switches.CanonicalAnchor.

Lemma decodeItemStringInitializationAnchorCanonicalOn
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  ⊢ ((⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I -∗ (decodeItemEntryAt800d6a24 args prefix rest))%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfold & %Hdomain & %Hframe & %Hprovenance & Hanchor & Hcont)".
iEval (unfold decodeItemEntryAt800d6a24).
zesu_pure_fact_hints_if_enabled.
iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemStringInitializationAnchorCanonicalWrongTarget
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) : True.
Proof.
Fail let registered := constr:(decodeItemStringInitializationAnchorCanonical args prefix rest n payloadStart lengthBytes frameBytes loaded) in
  let evidence := constr:(@zesu_canonical_anchor_intro Sigma (decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded) (decodeItemEntryAt800d6a24 args prefix rest) (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I registered) in
  let intro := constr:(@zesu_pure_fact_anchor_intro Sigma (decodeItemEntryAt800d6a24 args prefix rest) (decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded) (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I evidence :
    ZesuPureFactIntro ((decodeItemEntryAt800d6a24 args prefix rest) ∗ (decodeItemEntryAt800d6a24 args prefix rest))%I (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldStringHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I) in idtac.
exact I.
Qed.

Lemma decodeItemListInitializationAnchorCanonicalOn
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  ⊢ ((⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I -∗ (decodeItemEntryAt800d6ac4 args prefix rest))%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfold & %Hdomain & %Hframe & %Hprovenance & Hanchor & Hcont)".
iEval (unfold decodeItemEntryAt800d6ac4).
zesu_pure_fact_hints_if_enabled.
iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemListInitializationAnchorCanonicalWrongTarget
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) : True.
Proof.
Fail let registered := constr:(decodeItemListInitializationAnchorCanonical args prefix rest n payloadStart lengthBytes frameBytes loaded) in
  let evidence := constr:(@zesu_canonical_anchor_intro Sigma (decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded) (decodeItemEntryAt800d6ac4 args prefix rest) (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I registered) in
  let intro := constr:(@zesu_pure_fact_anchor_intro Sigma (decodeItemEntryAt800d6ac4 args prefix rest) (decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded) (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I evidence :
    ZesuPureFactIntro ((decodeItemEntryAt800d6ac4 args prefix rest) ∗ (decodeItemEntryAt800d6ac4 args prefix rest))%I (⌜decodeItemByteFoldFacts args n 0 payloadStart lengthBytes⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldListHeader args n 0 payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I) in idtac.
exact I.
Qed.

Lemma decodeItemStringSliceWitnessCanonicalOn
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) :
  ⊢ ((⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 183)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I -∗ (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I)%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfacts & Hanchor & Hcont)".
pose proof Hfacts as (_ & Hprovenance & _).
iEval (unfold decodeItemEntryAt800d6a14).
zesu_pure_fact_hints_if_enabled.
iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemStringSliceWitnessCanonicalWrongTarget
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) : True.
Proof.
Fail let registered := constr:(decodeItemStringSliceWitnessCanonical args prefix rest frameBytes oldAcc oldCursor loaded) in
  let evidence := constr:(@zesu_canonical_anchor_intro Sigma (decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
      frameBytes oldAcc oldCursor loaded) (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 183)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I registered) in
  let intro := constr:(@zesu_pure_fact_anchor_intro Sigma (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I (decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
      frameBytes oldAcc oldCursor loaded) (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 183)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I evidence :
    ZesuPureFactIntro ((∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I ∗ (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I)%I (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 183)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I) in idtac.
exact I.
Qed.

Lemma decodeItemListSliceWitnessCanonicalOn
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) :
  ⊢ ((⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 247)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I -∗ (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I)%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfacts & Hanchor & Hcont)".
pose proof Hfacts as (_ & Hprovenance & _).
iEval (unfold decodeItemEntryAt800d6ab4).
zesu_pure_fact_hints_if_enabled.
iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemListSliceWitnessCanonicalWrongTarget
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) : True.
Proof.
Fail let registered := constr:(decodeItemListSliceWitnessCanonical args prefix rest frameBytes oldAcc oldCursor loaded) in
  let evidence := constr:(@zesu_canonical_anchor_intro Sigma (decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
      frameBytes oldAcc oldCursor loaded) (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 247)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I registered) in
  let intro := constr:(@zesu_pure_fact_anchor_intro Sigma (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I (decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
      frameBytes oldAcc oldCursor loaded) (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 247)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I evidence :
    ZesuPureFactIntro ((∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I ∗ (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I)%I (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 247)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I) in idtac.
exact I.
Qed.

Lemma decodeItemStringReturnLengthWitnessCanonicalOn
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n payloadStart : Z) (bytes frameBytes : list byte) (loaded : bv 64) :
  ⊢ ((⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I -∗ (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength)%I)%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfacts & Hanchor & Hcont)".
pose proof Hfacts as (_ & _ & Hprovenance & _).
iEval (unfold decodeItemEntryAt800d6a40).
zesu_pure_fact_hints_if_enabled.
iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemStringReturnLengthWitnessCanonicalWrongTarget
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n payloadStart : Z) (bytes frameBytes : list byte) (loaded : bv 64) : True.
Proof.
Fail let registered := constr:(decodeItemStringReturnLengthWitnessCanonical args prefix rest n payloadStart bytes frameBytes loaded) in
  let evidence := constr:(@zesu_canonical_anchor_intro Sigma (decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded) (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength)%I (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I registered) in
  let intro := constr:(@zesu_pure_fact_anchor_intro Sigma (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength)%I (decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded) (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I evidence :
    ZesuPureFactIntro ((∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength)%I ∗ (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength)%I)%I (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I) in idtac.
exact I.
Qed.

Lemma decodeItemListReturnLengthWitnessCanonicalOn
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n payloadStart : Z) (bytes frameBytes : list byte) (loaded : bv 64) :
  ⊢ ((⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I -∗ (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength)%I)%I.
Proof.
iIntros "Hsource". iDestruct "Hsource" as "(%Hfacts & Hanchor & Hcont)".
pose proof Hfacts as (_ & _ & Hprovenance & _).
iEval (unfold decodeItemEntryAt800d6b08).
zesu_pure_fact_hints_if_enabled.
iFrame "Hanchor Hcont". iFrame "%".
Qed.

Lemma decodeItemListReturnLengthWitnessCanonicalWrongTarget
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) (n payloadStart : Z) (bytes frameBytes : list byte) (loaded : bv 64) : True.
Proof.
Fail let registered := constr:(decodeItemListReturnLengthWitnessCanonical args prefix rest n payloadStart bytes frameBytes loaded) in
  let evidence := constr:(@zesu_canonical_anchor_intro Sigma (decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded) (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength)%I (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I registered) in
  let intro := constr:(@zesu_pure_fact_anchor_intro Sigma (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength)%I (decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded) (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I evidence :
    ZesuPureFactIntro ((∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength)%I ∗ (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength)%I)%I (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I) in idtac.
exact I.
Qed.

Print Assumptions decodeItemStringInitializationAnchorCanonicalOff.
Print Assumptions decodeItemStringInitializationAnchorCanonicalOn.
Print Assumptions decodeItemStringInitializationAnchorCanonicalWrongTarget.
Print Assumptions decodeItemListInitializationAnchorCanonicalOff.
Print Assumptions decodeItemListInitializationAnchorCanonicalOn.
Print Assumptions decodeItemListInitializationAnchorCanonicalWrongTarget.
Print Assumptions decodeItemStringSliceWitnessCanonicalOff.
Print Assumptions decodeItemStringSliceWitnessCanonicalOn.
Print Assumptions decodeItemStringSliceWitnessCanonicalWrongTarget.
Print Assumptions decodeItemListSliceWitnessCanonicalOff.
Print Assumptions decodeItemListSliceWitnessCanonicalOn.
Print Assumptions decodeItemListSliceWitnessCanonicalWrongTarget.
Print Assumptions decodeItemStringReturnLengthWitnessCanonicalOff.
Print Assumptions decodeItemStringReturnLengthWitnessCanonicalOn.
Print Assumptions decodeItemStringReturnLengthWitnessCanonicalWrongTarget.
Print Assumptions decodeItemListReturnLengthWitnessCanonicalOff.
Print Assumptions decodeItemListReturnLengthWitnessCanonicalOn.
Print Assumptions decodeItemListReturnLengthWitnessCanonicalWrongTarget.
