Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Import ListNotations.
Open Scope Z_scope.

(* Generated resource wiring. No block-body proof is supplied. *)
(* Source: ZesuSsz/Contracts/DecodeItemBranchEntries.v; SHA-256: a206b82ea02ea581fe8c64b491c1b110c85ccdb90ed6ca0e8db9f286869bdaa6. *)
(* Source: ZesuSsz/Contracts/DecodeItemReturnFacts.v; SHA-256: 9da33c0898953f7ff5f270dc6e1f66681f4de045c7bb774b7701676399da1cf5. *)
(* Source: ZesuSsz/Contracts/DecodeItemSelected.v; SHA-256: a8d22f12124a5c2eace1696bb13de3e774caa0e1b2a354819c03bffec26fe804. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemBlockEntries.v; SHA-256: dbde7a5579c890bb171b276a922c8c226babb927668e78191c2e24de6a1c1017. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemByteFold.v; SHA-256: 6f80226eadadd5468b46aebc8c48561f54815f94c1989e465d530f6896e4237d. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemByteFoldBlocks.v; SHA-256: a504dfa090e1ec91f709ad3c3b5c7df1823dc64159b0b53960a0606a5ffe92a9. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemContract.v; SHA-256: 595fab72b6fcaa0603a8bd35f5e3b4433a380493a076f2bf8d05116738355d9a. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemFoldEntries.v; SHA-256: b8a3d631d1825f15220d1f586bd34592b78aceee61781018a36450f353c4c57a. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemReturnImageDef.v; SHA-256: 9e53a7c256d3a41bc0c560c8ccbdb5ccd90e3f0434610f7891253ff4e6f57ed2. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemReturnImages.v; SHA-256: bf85e61fe8c5a6554b371df3943d119315447673d17143070f5bbfefeef6fce0. *)
(* Source: ZesuSsz/Evidence/decode_item_block_design.json; SHA-256: 3412eb7aaadb76eb2a8fecfac23dcb2763f56060884e765cb3c12601db739dd9. *)
(* Source: build/stock-zisk/cfg.json; SHA-256: 98c4614e6ff7b6e1cb85bdc3b9e600dd85eccd5afacda8b1c5b75ff66db16fc2. *)
(* Source: build/stock-zisk/decodeItem.raw.dump; SHA-256: 411a66f2da6ccf7604a95353f3ff89868cb4382b4cf304196926311a95330f7a. *)
(* Source: build/stock-zisk/inventory.json; SHA-256: 7ac1a2169d150975aec1e66369e4cb19a4a7f20e12a485f5c1a3ac46e224e12d. *)
(* Source: tools/block/generate_table.py; SHA-256: 809e1cb213a910d5409fe126979684b3239a5b20464ccb1ae887fe6f20cb21ac. *)

Section decode_item_block_table.
Context `{!islaG Sigma} `{!threadG}.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6960. Body proof: pending. *)
Definition decodeItemState800d6960 : iProp Sigma :=
  (∃ (returnAddress : Z) (args : DecodeItemArgs), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6960 (returnAddress) (args))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974. Body proof: pending. *)
Definition decodeItemState800d6974 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974 (args) (frameBytes) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d697c. Body proof: pending. *)
Definition decodeItemState800d697c : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d697c (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c. Body proof: pending. *)
Definition decodeItemState800d698c : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (x11 : bv 64) (x12 : bv 64) (x13 : bv 64) (x14 : bv 64) (x15 : bv 64) (x16 : bv 64) (outputBytes : list byte) (frameBytes : list byte) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (x11) (x12) (x13) (x14) (x15) (x16) (outputBytes) (frameBytes) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69a4. Body proof: pending. *)
Definition decodeItemState800d69a4 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69a4 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d69b0. Body proof: pending. *)
Definition decodeItemState800d69b0 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d69b0 (args) (locals) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69d8. Body proof: pending. *)
Definition decodeItemState800d69d8 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69d8 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e0. Body proof: pending. *)
Definition decodeItemState800d69e0 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e0 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e8. Body proof: pending. *)
Definition decodeItemState800d69e8 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e8 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a00. Body proof: pending. *)
Definition decodeItemState800d6a00 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a00 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a08. Body proof: pending. *)
Definition decodeItemState800d6a08 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a08 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a14. Body proof: pending. *)
Definition decodeItemState800d6a14 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a14 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24. Body proof: pending. *)
Definition decodeItemState800d6a24 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24 (args) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38. Body proof: pending. *)
Definition decodeItemState800d6a38 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40. Body proof: pending. *)
Definition decodeItemState800d6a40 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40 (args) (locals) (inputPrefix) (rest) (headerLength) (payloadLength))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a64. Body proof: pending. *)
Definition decodeItemState800d6a64 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a64 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a6c. Body proof: pending. *)
Definition decodeItemState800d6a6c : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a6c (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a78. Body proof: pending. *)
Definition decodeItemState800d6a78 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a78 (args) (locals) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6aa8. Body proof: pending. *)
Definition decodeItemState800d6aa8 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6aa8 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ab4. Body proof: pending. *)
Definition decodeItemState800d6ab4 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ab4 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6ac4. Body proof: pending. *)
Definition decodeItemState800d6ac4 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6ac4 (args) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ad8. Body proof: pending. *)
Definition decodeItemState800d6ad8 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ad8 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0. Body proof: pending. *)
Definition decodeItemState800d6ae0 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (locals))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08. Body proof: pending. *)
Definition decodeItemState800d6b08 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08 (args) (locals) (inputPrefix) (rest) (headerLength) (payloadLength))%I.

Definition decodeItemBlockTable : blockTable Sigma :=
  {| block_table_code := ZesuSsz.Contracts.DecodeItemSelected.decodeItemSelectedCode;
     block_table_entries := [(0x800d6960, decodeItemState800d6960);
   (0x800d6974, decodeItemState800d6974);
   (0x800d697c, decodeItemState800d697c);
   (0x800d698c, decodeItemState800d698c);
   (0x800d69a4, decodeItemState800d69a4);
   (0x800d69b0, decodeItemState800d69b0);
   (0x800d69d8, decodeItemState800d69d8);
   (0x800d69e0, decodeItemState800d69e0);
   (0x800d69e8, decodeItemState800d69e8);
   (0x800d6a00, decodeItemState800d6a00);
   (0x800d6a08, decodeItemState800d6a08);
   (0x800d6a14, decodeItemState800d6a14);
   (0x800d6a24, decodeItemState800d6a24);
   (0x800d6a38, decodeItemState800d6a38);
   (0x800d6a40, decodeItemState800d6a40);
   (0x800d6a64, decodeItemState800d6a64);
   (0x800d6a6c, decodeItemState800d6a6c);
   (0x800d6a78, decodeItemState800d6a78);
   (0x800d6aa8, decodeItemState800d6aa8);
   (0x800d6ab4, decodeItemState800d6ab4);
   (0x800d6ac4, decodeItemState800d6ac4);
   (0x800d6ad8, decodeItemState800d6ad8);
   (0x800d6ae0, decodeItemState800d6ae0);
   (0x800d6b08, decodeItemState800d6b08)] |}.

(* Completion requires the persistent code resource and every block body. *)
Definition decodeItemBlockTable_complete :=
  block_table_complete decodeItemBlockTable.

End decode_item_block_table.

Definition decodeItemBlockEdges : list (Z * Z) :=
  [(0x800d6960, 0x800d6ae0);
   (0x800d6960, 0x800d6974);
   (0x800d6974, 0x800d69a4);
   (0x800d6974, 0x800d697c);
   (0x800d697c, 0x800d698c);
   (0x800d69a4, 0x800d69d8);
   (0x800d69a4, 0x800d69b0);
   (0x800d69d8, 0x800d6a00);
   (0x800d69d8, 0x800d69e0);
   (0x800d69e0, 0x800d6ae0);
   (0x800d69e0, 0x800d69e8);
   (0x800d69e8, 0x800d698c);
   (0x800d6a00, 0x800d6a64);
   (0x800d6a00, 0x800d6a08);
   (0x800d6a08, 0x800d6ae0);
   (0x800d6a08, 0x800d6a14);
   (0x800d6a14, 0x800d6a24);
   (0x800d6a24, 0x800d6a24);
   (0x800d6a24, 0x800d6a38);
   (0x800d6a38, 0x800d6ae0);
   (0x800d6a38, 0x800d6a40);
   (0x800d6a64, 0x800d6aa8);
   (0x800d6a64, 0x800d6a6c);
   (0x800d6a6c, 0x800d6ae0);
   (0x800d6a6c, 0x800d6a78);
   (0x800d6aa8, 0x800d6ae0);
   (0x800d6aa8, 0x800d6ab4);
   (0x800d6ab4, 0x800d6ac4);
   (0x800d6ac4, 0x800d6ac4);
   (0x800d6ac4, 0x800d6ad8);
   (0x800d6ad8, 0x800d6b08);
   (0x800d6ad8, 0x800d6ae0)].

Definition decodeItemBlockReturns : list (Z * Z) :=
  [(0x800d698c, 0x800d69a0);
   (0x800d69b0, 0x800d69d4);
   (0x800d6a40, 0x800d6a60);
   (0x800d6a78, 0x800d6aa4);
   (0x800d6ae0, 0x800d6b04);
   (0x800d6b08, 0x800d6b2c)].

Print Assumptions decodeItemBlockTable_complete.
