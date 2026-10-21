Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith.
From lithium Require Import lvar.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.

Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Lemma loop_header_resource_first_equiv `{!islaG Sigma} `{!threadG}
 (args : DecodeItemArgs) (prefix : byte) (rest : list byte) :
 decodeItemEntryAt800d6a24 args prefix rest ⊣⊢ (∃ (n : lvar "zesuLoopCount" Z) (i : lvar "zesuLoopIndex" Z) (payloadStart : Z) (lengthBytes frameBytes : list byte)
       (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
    decodeItemByteFoldStringHeader args n i payloadStart
      lengthBytes frameBytes loaded ∗
    decodeItemBranchContinuation args)%I.
Proof.
 rewrite /decodeItemEntryAt800d6a24.
 iSplit.
 - iIntros "(%n & %i & %ps & %lb & %fb & %loaded & Hheader & Hfacts & Hcont)".
   iExists n,i,ps,lb,fb,loaded. iFrame.
 - iIntros "(%n & %i & %ps & %lb & %fb & %loaded & Hfacts & Hheader & Hcont)".
   iExists n,i,ps,lb,fb,loaded. iFrame.
Qed.
Print Assumptions loop_header_resource_first_equiv.
