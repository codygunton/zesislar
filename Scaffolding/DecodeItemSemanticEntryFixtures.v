Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Section Bindings.
Context `{!islaG Sigma} `{!threadG}.
Definition binding800d6960 (returnAddress : Z) (args : DecodeItemArgs) : iProp Sigma :=
  ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemEntryResources ((decodeItemDomainAt returnAddress decodeItemC1BDomain)) (args).
Definition binding800d6974 (args : DecodeItemArgs) (frameBytes : list byte) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974 (args) (frameBytes) (inputPrefix) (rest).
Definition binding800d697c (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d697c (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d698c (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (pointerBytes : list byte) (lengthBytes : list byte) (inputPrefix : byte) (rest : list byte) (isLiteral : bool) : iProp Sigma :=
  ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (locals) (pointerBytes) (lengthBytes) (inputPrefix) (rest) (isLiteral).
Definition binding800d69a4 (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69a4 (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d69b0 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d69b0 (args) (locals) (inputPrefix) (rest).
Definition binding800d69d8 (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69d8 (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d69e0 (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e0 (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d69e8 (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e8 (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d6a00 (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a00 (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d6a08 (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a08 (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d6a14 (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a14 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded) (inputPrefix) (rest).
Definition binding800d6a24 (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24 (args) (inputPrefix) (rest).
Definition binding800d6a38 (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) (inputPrefix) (rest).
Definition binding800d6a40 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z) : iProp Sigma :=
  ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40 (args) (locals) (inputPrefix) (rest) (headerLength) (payloadLength).
Definition binding800d6a64 (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a64 (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d6a6c (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a6c (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d6a78 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a78 (args) (locals) (inputPrefix) (rest).
Definition binding800d6aa8 (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6aa8 (args) (frameBytes) (x13) (inputPrefix) (rest).
Definition binding800d6ab4 (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ab4 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded) (inputPrefix) (rest).
Definition binding800d6ac4 (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6ac4 (args) (inputPrefix) (rest).
Definition binding800d6ad8 (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte) : iProp Sigma :=
  ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ad8 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) (inputPrefix) (rest).
Definition binding800d6ae0 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) : iProp Sigma :=
  ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (locals).
Definition binding800d6b08 (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z) : iProp Sigma :=
  ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08 (args) (locals) (inputPrefix) (rest) (headerLength) (payloadLength).
End Bindings.

Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemPathAgreement.
Lemma decodeItemSailSuccessCompatibility args isList headerLength payloadLength :
  ZesuSsz.Compliance.DecodeItemPathAgreement.decodeItemSailSuccess
    args isList headerLength payloadLength <->
  ZesuSsz.Contracts.DecodeItemReturnFacts.decodeItemSailSuccess
    args isList headerLength payloadLength.
Proof. reflexivity. Qed.
Print Assumptions decodeItemSailSuccessCompatibility.
