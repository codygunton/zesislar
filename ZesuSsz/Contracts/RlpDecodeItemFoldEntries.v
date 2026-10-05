From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.

(* The header entries retain the complete Q27 machine resources. *)
Definition decodeItemEntryAt800d6a24 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  (∃ (n i payloadStart : Z) (lengthBytes frameBytes : list byte)
       (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
    decodeItemByteFoldStringHeader args n i payloadStart
      lengthBytes frameBytes loaded ∗
    decodeItemBranchContinuation args)%I.

Definition decodeItemEntryAt800d6ac4 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  (∃ (n i payloadStart : Z) (lengthBytes frameBytes : list byte)
       (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
    decodeItemByteFoldListHeader args n i payloadStart
      lengthBytes frameBytes loaded ∗
    decodeItemBranchContinuation args)%I.

(* Body entries use the same guard and resources as their headers. *)
Definition decodeItemBodyAt800d6a24 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  (∃ (n i payloadStart : Z) (lengthBytes frameBytes : list byte)
       (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
    decodeItemByteFoldStringHeader args n i payloadStart
      lengthBytes frameBytes loaded ∗
    decodeItemBranchContinuation args)%I.

Definition decodeItemBodyAt800d6ac4 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  (∃ (n i payloadStart : Z) (lengthBytes frameBytes : list byte)
       (loaded : bv 64),
    ⌜i < n /\
      decodeItemDomainAt (decodeItemReturnAddress args)
        decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
    decodeItemByteFoldListHeader args n i payloadStart
      lengthBytes frameBytes loaded ∗
    decodeItemBranchContinuation args)%I.
