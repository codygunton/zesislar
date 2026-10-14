Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Compliance.DecodeItemOutputWitnessSelections.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemLiteralOutputWitnessOff `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (a3 a4 a5 a6 : bv 64) frameBytes :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest -> bv_unsigned prefix <= 127 ->
  decodeItemAcceptedFacts args false 0 1 ->
  ⊢ (decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
    (Z_to_bv 64 (decodeItemInputPointer args)) 1 a3 a4 a5 a6 1 frameBytes) -∗
    decodeItemJoin698cTarget args prefix rest true)%I.
Proof.
  intros Hdomain Hhead Hclass Haccepted. iIntros "Hcore".
  Fail zesu_pure_fact_hints_if_enabled.
  pose proof (decodeItemLiteralOutputWitness args prefix rest) as Hintro.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro in Hintro.
  iApply Hintro. iSplit; first (iPureIntro; repeat first [assumption | split]).
  iExists a3, a4, a5, a6, frameBytes. iFrame.
Qed.

Lemma decodeItemShortStringOutputWitnessOff `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (payloadLength a3 a4 a5 a6 : bv 64) frameBytes :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest -> 129 <= bv_unsigned prefix <= 183 ->
  bv_unsigned payloadLength = bv_unsigned prefix - 128 ->
  decodeItemAcceptedFacts args false 1 (bv_unsigned prefix - 128) ->
  ⊢ (decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
    (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) (bv_add payloadLength 1)
    a3 a4 a5 a6 payloadLength frameBytes) -∗
    decodeItemJoin698cTarget args prefix rest false)%I.
Proof.
  intros Hdomain Hhead Hclass Hlength Haccepted. iIntros "Hcore".
  Fail zesu_pure_fact_hints_if_enabled.
  pose proof (decodeItemShortStringOutputWitness args prefix rest payloadLength) as Hintro.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro in Hintro.
  iApply Hintro. iSplit; first (iPureIntro; repeat first [assumption | split]).
  iExists a3, a4, a5, a6, frameBytes. iFrame.
Qed.

Require Import ZesuSsz.Automation.Switches.PureFactHints.

Lemma decodeItemLiteralOutputWitnessOn `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (a3 a4 a5 a6 : bv 64) frameBytes :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest -> bv_unsigned prefix <= 127 ->
  decodeItemAcceptedFacts args false 0 1 ->
  ⊢ (decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
    (Z_to_bv 64 (decodeItemInputPointer args)) 1 a3 a4 a5 a6 1 frameBytes) -∗
    decodeItemJoin698cTarget args prefix rest true)%I.
Proof.
  intros Hdomain Hhead Hclass Haccepted. iIntros "Hcore".
  iEval (unfold decodeItemReturnEntryCore) in "Hcore".
  iDestruct "Hcore" as "(Hsys & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %HcoreFacts & Hcont & _)".
  iEval (cbn [decodeItemRawOutputLocals returnStorage]) in "Hout".
  zesu_pure_fact_hints_if_enabled.
  iSplit; first (iPureIntro; repeat first [assumption | split]).
  iExists a3, a4, a5, a6, frameBytes.
  unfold decodeItemReturnEntryCore.
  iFrame "Hsys H10 H11 H12 H13 H14 H15 H16 H2 H1 H8 Hin Hout Hstack Hcont".
  iPureIntro. exact HcoreFacts.
Qed.

Lemma decodeItemShortStringOutputWitnessOn `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (payloadLength a3 a4 a5 a6 : bv 64) frameBytes :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest -> 129 <= bv_unsigned prefix <= 183 ->
  bv_unsigned payloadLength = bv_unsigned prefix - 128 ->
  decodeItemAcceptedFacts args false 1 (bv_unsigned prefix - 128) ->
  ⊢ (decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
    (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) (bv_add payloadLength 1)
    a3 a4 a5 a6 payloadLength frameBytes) -∗
    decodeItemJoin698cTarget args prefix rest false)%I.
Proof.
  intros Hdomain Hhead Hclass Hlength Haccepted. iIntros "Hcore".
  iEval (unfold decodeItemReturnEntryCore) in "Hcore".
  iDestruct "Hcore" as "(Hsys & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %HcoreFacts & Hcont & _)".
  iEval (cbn [decodeItemRawOutputLocals returnStorage]) in "Hout".
  zesu_pure_fact_hints_if_enabled.
  iSplit; first (iPureIntro; repeat first [assumption | split]).
  iExists a3, a4, a5, a6, frameBytes.
  unfold decodeItemReturnEntryCore.
  iFrame "Hsys H10 H11 H12 H13 H14 H15 H16 H2 H1 H8 Hin Hout Hstack Hcont".
  iPureIntro. exact HcoreFacts.
Qed.

Lemma decodeItemLiteralOutputExpandedDirect `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (a3 a4 a5 a6 : bv 64) frameBytes :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest -> bv_unsigned prefix <= 127 ->
  decodeItemAcceptedFacts args false 0 1 ->
  ⊢ (decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
    (Z_to_bv 64 (decodeItemInputPointer args)) 1 a3 a4 a5 a6 1 frameBytes) -∗
    ∃ (locals : DecodeItemReturnLocals) (pointerBytes lengthBytes : list byte),
      decodeItemEntryAt800d698c args locals pointerBytes lengthBytes prefix rest true)%I.
Proof.
  intros Hdomain Hhead Hclass Haccepted. iIntros "Hcore".
  iEval (unfold decodeItemReturnEntryCore) in "Hcore".
  iDestruct "Hcore" as "(Hsys & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %HcoreFacts & Hcont & _)".
  iEval (cbn [decodeItemRawOutputLocals returnStorage]) in "Hout".
  pose proof (decodeItemLiteralOutputWitness args prefix rest) as Hintro.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro, decodeItemJoin698cTarget in Hintro.
  iApply Hintro.
  iSplit; first (iPureIntro; repeat first [assumption | split]).
  iExists a3, a4, a5, a6, frameBytes.
  unfold decodeItemReturnEntryCore.
  iFrame "Hsys H10 H11 H12 H13 H14 H15 H16 H2 H1 H8 Hin Hout Hstack Hcont".
  iPureIntro. exact HcoreFacts.
Qed.

Lemma decodeItemShortStringOutputExpandedDirect `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (payloadLength a3 a4 a5 a6 : bv 64) frameBytes :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemInputHead args prefix rest -> 129 <= bv_unsigned prefix <= 183 ->
  bv_unsigned payloadLength = bv_unsigned prefix - 128 ->
  decodeItemAcceptedFacts args false 1 (bv_unsigned prefix - 128) ->
  ⊢ (decodeItemReturnEntryCore args (decodeItemRawOutputLocals args
    (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) 1) (bv_add payloadLength 1)
    a3 a4 a5 a6 payloadLength frameBytes) -∗
    ∃ (locals : DecodeItemReturnLocals) (pointerBytes lengthBytes : list byte),
      decodeItemEntryAt800d698c args locals pointerBytes lengthBytes prefix rest false)%I.
Proof.
  intros Hdomain Hhead Hclass Hlength Haccepted. iIntros "Hcore".
  iEval (unfold decodeItemReturnEntryCore) in "Hcore".
  iDestruct "Hcore" as "(Hsys & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %HcoreFacts & Hcont & _)".
  iEval (cbn [decodeItemRawOutputLocals returnStorage]) in "Hout".
  pose proof (decodeItemShortStringOutputWitness args prefix rest payloadLength) as Hintro.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro, decodeItemJoin698cTarget in Hintro.
  iApply Hintro.
  iSplit; first (iPureIntro; repeat first [assumption | split]).
  iExists a3, a4, a5, a6, frameBytes.
  unfold decodeItemReturnEntryCore.
  iFrame "Hsys H10 H11 H12 H13 H14 H15 H16 H2 H1 H8 Hin Hout Hstack Hcont".
  iPureIntro. exact HcoreFacts.
Qed.

Print Assumptions decodeItemLiteralOutputWitnessOff.
Print Assumptions decodeItemShortStringOutputWitnessOff.
Print Assumptions decodeItemLiteralOutputWitnessOn.
Print Assumptions decodeItemShortStringOutputWitnessOn.
Print Assumptions decodeItemLiteralOutputExpandedDirect.
Print Assumptions decodeItemShortStringOutputExpandedDirect.
