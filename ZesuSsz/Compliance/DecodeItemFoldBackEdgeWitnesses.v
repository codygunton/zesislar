Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Compliance.DecodeItemJoinTransferPure.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Open Scope Z_scope.

#[export] Instance decodeItemStringBackEdgeAnchor
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n i payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  @ZesuPureFactAnchor Sigma (decodeItemEntryAt800d6a24 args prefix rest)
    (decodeItemByteFoldStringHeader args n (i + 1) payloadStart lengthBytes frameBytes loaded)
    (⌜i + 1 < n⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldStringHeader args n (i + 1) payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%Hguard & %Hdomain & %Hframe & %Hprovenance & Hheader & Hcont)".
  iApply (decodeItemStringHeaderIntro args prefix rest n (i + 1) payloadStart
    lengthBytes frameBytes loaded Hguard Hdomain Hframe Hprovenance).
  iFrame.
Qed.

#[export] Instance decodeItemListBackEdgeAnchor
    `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte)
    (n i payloadStart : Z) (lengthBytes frameBytes : list byte) (loaded : bv 64) :
  @ZesuPureFactAnchor Sigma (decodeItemEntryAt800d6ac4 args prefix rest)
    (decodeItemByteFoldListHeader args n (i + 1) payloadStart lengthBytes frameBytes loaded)
    (⌜i + 1 < n⌝ ∗
     ⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args⌝ ∗
     ⌜decodeItemSavedFrameFacts args frameBytes⌝ ∗
     ⌜decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
     decodeItemByteFoldListHeader args n (i + 1) payloadStart lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%Hguard & %Hdomain & %Hframe & %Hprovenance & Hheader & Hcont)".
  iApply (decodeItemListHeaderIntro args prefix rest n (i + 1) payloadStart
    lengthBytes frameBytes loaded Hguard Hdomain Hframe Hprovenance).
  iFrame.
Qed.


Print Assumptions decodeItemStringBackEdgeAnchor.
Print Assumptions decodeItemListBackEdgeAnchor.
