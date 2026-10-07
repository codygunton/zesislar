From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Import ListNotations.
Open Scope Z_scope.

(* A pending edge proof starts at a concrete block entry. It must hand
   its resources to the entry contract at the exact join PC. *)
Definition decodeItemJoinTransferObligation `{!islaG Sigma} `{!threadG}
    (sourcePc joinPc : Z) (sourceEntry joinEntry : iProp Sigma) : iProp Sigma :=
  (decodeItemSelectedCode -∗
   instr_body sourcePc
     (sourceEntry ∗ instr_pre joinPc (joinEntry ∗ True) ∗ True))%I.

Definition decodeItemJoin698cTarget `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte)
    (isLiteral : bool) : iProp Sigma :=
  (∃ (locals : DecodeItemReturnLocals) (pointerBytes lengthBytes : list byte),
    decodeItemEntryAt800d698c args locals pointerBytes lengthBytes inputPrefix rest isLiteral)%I.

Definition decodeItemJoin6ae0Target `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  (∃ locals : DecodeItemReturnLocals,
    decodeItemEntryAt800d6ae0 args locals)%I.

Definition decodeItemJoin698cFrom697c `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d697c 0x800d698c
    (decodeItemEntryAt800d697c args frameBytes prefix inputPrefix rest)
    (decodeItemJoin698cTarget args inputPrefix rest true).

Definition decodeItemJoin698cFrom69e8 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (payloadLength : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d69e8 0x800d698c
    (decodeItemEntryAt800d69e8 args frameBytes payloadLength inputPrefix rest)
    (decodeItemJoin698cTarget args inputPrefix rest false).

Definition decodeItemJoin6a24From6a14 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte)
    (oldAcc oldCursor loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6a14 0x800d6a24
    (decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
       oldAcc oldCursor loaded inputPrefix rest)
    (decodeItemEntryAt800d6a24 args inputPrefix rest).

(* The backedge keeps args and frameBytes unchanged. These lemmas retain
   only their pure facts; they do not prove machine preservation. *)
Lemma decodeItemBackedgeDomainAtPreserved (args : DecodeItemArgs) :
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args.
Proof. exact (fun Hdomain => Hdomain). Qed.

Lemma decodeItemBackedgeSavedFrameFactsPreserved
    (args : DecodeItemArgs) (frameBytes : list byte) :
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemSavedFrameFacts args frameBytes.
Proof. exact (fun Hframe => Hframe). Qed.

Definition decodeItemJoin6a24Backedge `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6a24 0x800d6a24
    (⌜i + 1 < n /\
       decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
       decodeItemSavedFrameFacts args frameBytes /\
       decodeItemFoldProvenance args false inputPrefix rest n payloadStart lengthBytes⌝ ∗
     "PC" ↦ᵣ RVal_Bits (Z_to_bv 64 0x800d6a24) ∗
     decodeItemByteFoldStringHeader args n i payloadStart
       lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I
    (decodeItemEntryAt800d6a24 args inputPrefix rest).

Definition decodeItemJoin6ac4From6ab4 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte)
    (oldAcc oldCursor loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6ab4 0x800d6ac4
    (decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
       oldAcc oldCursor loaded inputPrefix rest)
    (decodeItemEntryAt800d6ac4 args inputPrefix rest).

Definition decodeItemJoin6ac4Backedge `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6ac4 0x800d6ac4
    (⌜i + 1 < n /\
       decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
       decodeItemSavedFrameFacts args frameBytes /\
       decodeItemFoldProvenance args true inputPrefix rest n payloadStart lengthBytes⌝ ∗
     "PC" ↦ᵣ RVal_Bits (Z_to_bv 64 0x800d6ac4) ∗
     decodeItemByteFoldListHeader args n i payloadStart
       lengthBytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I
    (decodeItemEntryAt800d6ac4 args inputPrefix rest).

(* The zero-length path includes the prologue at 0x800d6960. Its branch
   at 0x800d6970 reaches the error join. *)
Definition decodeItemJoin6ae0From6970 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6960 0x800d6ae0
    (⌜decodeItemInputLength args = 0⌝ ∗
     decodeItemEntryResources decodeItemC1BDomain args ∗
     decodeItemBranchContinuation args)%I
    (decodeItemJoin6ae0Target args).

Definition decodeItemJoin6ae0From69e0 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (lengthRegister : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d69e0 0x800d6ae0
    (⌜Z.land (bv_unsigned lengthRegister) 127 >=
       decodeItemInputLength args⌝ ∗
     decodeItemEntryAt800d69e0 args frameBytes lengthRegister inputPrefix rest)%I
    (decodeItemJoin6ae0Target args).

Definition decodeItemJoin6ae0From6a08 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6a08 0x800d6ae0
    (⌜bv_unsigned (Z_to_bv 8 (bv_unsigned prefix + 73)) >=
       decodeItemInputLength args⌝ ∗
     decodeItemEntryAt800d6a08 args frameBytes prefix inputPrefix rest)%I
    (decodeItemJoin6ae0Target args).

Definition decodeItemJoin6ae0From6a38 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6a38 0x800d6ae0
    (⌜decodeItemFoldLengthFits args n lengthBytes = false⌝ ∗
     decodeItemEntryAt800d6a38 args n payloadStart
       lengthBytes frameBytes loaded inputPrefix rest)%I
    (decodeItemJoin6ae0Target args).

Definition decodeItemJoin6ae0From6a6c `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6a6c 0x800d6ae0
    (⌜bv_unsigned (Z_to_bv 8 (bv_unsigned prefix + 64)) >=
       decodeItemInputLength args⌝ ∗
     decodeItemEntryAt800d6a6c args frameBytes prefix inputPrefix rest)%I
    (decodeItemJoin6ae0Target args).

Definition decodeItemJoin6ae0From6aa8 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (frameBytes : list byte)
    (prefix : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6aa8 0x800d6ae0
    (⌜bv_unsigned (Z_to_bv 8 (bv_unsigned prefix + 9)) >=
       decodeItemInputLength args⌝ ∗
     decodeItemEntryAt800d6aa8 args frameBytes prefix inputPrefix rest)%I
    (decodeItemJoin6ae0Target args).

Definition decodeItemJoin6ae0From6ad8 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  decodeItemJoinTransferObligation 0x800d6ad8 0x800d6ae0
    (⌜decodeItemFoldLengthFits args n lengthBytes = false⌝ ∗
     decodeItemEntryAt800d6ad8 args n payloadStart
       lengthBytes frameBytes loaded inputPrefix rest)%I
    (decodeItemJoin6ae0Target args).
