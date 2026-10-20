From Coq Require Import List ZArith.
From lithium Require Import lvar.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.

(* The header entries retain the complete Q27 machine resources. *)
Definition decodeItemEntryAt800d6a24 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (n : lvar "zesuLoopCount" Z) (i : lvar "zesuLoopIndex" Z) (payloadStart : Z) (lengthBytes frameBytes : list byte)
       (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
    decodeItemByteFoldStringHeader args n i payloadStart
      lengthBytes frameBytes loaded ∗
    decodeItemBranchContinuation args)%I.

Definition decodeItemEntryAt800d6ac4 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (n : lvar "zesuLoopCount" Z) (i : lvar "zesuLoopIndex" Z) (payloadStart : Z) (lengthBytes frameBytes : list byte)
       (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
    decodeItemByteFoldListHeader args n i payloadStart
      lengthBytes frameBytes loaded ∗
    decodeItemBranchContinuation args)%I.

(* Body entries use the same guard and resources as their headers. *)
Definition decodeItemBodyAt800d6a24 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (n : lvar "zesuLoopCount" Z) (i : lvar "zesuLoopIndex" Z) (payloadStart : Z) (lengthBytes frameBytes : list byte)
       (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes⌝ ∗
    decodeItemByteFoldStringHeader args n i payloadStart
      lengthBytes frameBytes loaded ∗
    decodeItemBranchContinuation args)%I.

Definition decodeItemBodyAt800d6ac4 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (prefix : byte) (rest : list byte) : iProp Sigma :=
  (∃ (n : lvar "zesuLoopCount" Z) (i : lvar "zesuLoopIndex" Z) (payloadStart : Z) (lengthBytes frameBytes : list byte)
       (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes⌝ ∗
    decodeItemByteFoldListHeader args n i payloadStart
      lengthBytes frameBytes loaded ∗
    decodeItemBranchContinuation args)%I.
