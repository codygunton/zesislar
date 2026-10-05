Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Import ListNotations.
Open Scope Z_scope.

(* Generated resource wiring. No block-body proof is supplied. *)
(* Source: ZesuSsz/Contracts/DecodeItemBranchEntries.v; SHA-256: fdb4745bb3bf98fb29423f33c7394e6c7eb69834f2eb4ee511d96e5277be37bf. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemBlockEntries.v; SHA-256: 8798c664659147643f4b6f5749c26962630d6899db5a258ec8f49517f76be830. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemByteFold.v; SHA-256: 5a910afa091a42cfb2a8847592918baf0b67cbd62a830c384817834c1943328b. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemByteFoldBlocks.v; SHA-256: 3e86d45004fafe935b02cfa02c9ea1fd0e80c313df7b38775b252bc67c44b6ec. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemContract.v; SHA-256: fecb4272bbe1e7a96e650f2e113843bc886ea137c1a3e6d5ab1dfe53de5e7fc1. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemFoldEntries.v; SHA-256: a7415475adb13eed8a3d23c9f3aac9c6eca94bb635a4b53685934307692bb803. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemReturnImageDef.v; SHA-256: 9e53a7c256d3a41bc0c560c8ccbdb5ccd90e3f0434610f7891253ff4e6f57ed2. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemReturnImages.v; SHA-256: 16d16546759e850d362bd1d8c36d4e1f0708c8cfe7c5d6180abb0f629f6bba6d. *)
(* Source: ZesuSsz/Evidence/decode_item_block_design.json; SHA-256: d216e76eff7a6a4be4ad8bcd02d6f0d567a90b287b4361543171eafbca3dba64. *)
(* Source: build/stock-zisk/cfg.json; SHA-256: 98c4614e6ff7b6e1cb85bdc3b9e600dd85eccd5afacda8b1c5b75ff66db16fc2. *)
(* Source: build/stock-zisk/decodeItem.raw.dump; SHA-256: 411a66f2da6ccf7604a95353f3ff89868cb4382b4cf304196926311a95330f7a. *)
(* Source: build/stock-zisk/inventory.json; SHA-256: 7ac1a2169d150975aec1e66369e4cb19a4a7f20e12a485f5c1a3ac46e224e12d. *)
(* Source: tools/block/generate_table.py; SHA-256: 277970112715cdf780dc4552598e83b1bf92591866b88625e62d7c6d06b9afcd. *)

Section decode_item_block_table.
Context `{!islaG Sigma} `{!threadG}.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemEntryResources. Body proof: pending. *)
Definition decodeItemState800d6960 : iProp Sigma :=
  (∀ (returnAddress : Z) (args : DecodeItemArgs), ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemEntryResources ((decodeItemDomainAt returnAddress decodeItemC1BDomain)) (args))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974. Body proof: pending. *)
Definition decodeItemState800d6974 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974 (args) (frameBytes))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d697c. Body proof: pending. *)
Definition decodeItemState800d697c : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d697c (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c. Body proof: pending. *)
Definition decodeItemState800d698c : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (pointerBytes : list byte) (lengthBytes : list byte), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (locals) (pointerBytes) (lengthBytes))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69a4. Body proof: pending. *)
Definition decodeItemState800d69a4 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69a4 (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d69b0. Body proof: pending. *)
Definition decodeItemState800d69b0 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d69b0 (args) (locals))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69d8. Body proof: pending. *)
Definition decodeItemState800d69d8 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69d8 (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e0. Body proof: pending. *)
Definition decodeItemState800d69e0 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e0 (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e8. Body proof: pending. *)
Definition decodeItemState800d69e8 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e8 (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a00. Body proof: pending. *)
Definition decodeItemState800d6a00 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a00 (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a08. Body proof: pending. *)
Definition decodeItemState800d6a08 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a08 (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a14. Body proof: pending. *)
Definition decodeItemState800d6a14 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a14 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24. Body proof: pending. *)
Definition decodeItemState800d6a24 : iProp Sigma :=
  (∀ (args : DecodeItemArgs), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24 (args))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38. Body proof: pending. *)
Definition decodeItemState800d6a38 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40. Body proof: pending. *)
Definition decodeItemState800d6a40 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40 (args) (locals))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a64. Body proof: pending. *)
Definition decodeItemState800d6a64 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a64 (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a6c. Body proof: pending. *)
Definition decodeItemState800d6a6c : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a6c (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a78. Body proof: pending. *)
Definition decodeItemState800d6a78 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a78 (args) (locals))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6aa8. Body proof: pending. *)
Definition decodeItemState800d6aa8 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6aa8 (args) (frameBytes) (x13))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ab4. Body proof: pending. *)
Definition decodeItemState800d6ab4 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ab4 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6ac4. Body proof: pending. *)
Definition decodeItemState800d6ac4 : iProp Sigma :=
  (∀ (args : DecodeItemArgs), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6ac4 (args))%I.

(* Entry: ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ad8. Body proof: pending. *)
Definition decodeItemState800d6ad8 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ad8 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0. Body proof: pending. *)
Definition decodeItemState800d6ae0 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (locals))%I.

(* Entry: ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08. Body proof: pending. *)
Definition decodeItemState800d6b08 : iProp Sigma :=
  (∀ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08 (args) (locals))%I.

Definition decodeItemBlockTable : blockTable Sigma :=
  [(0x800d6960, decodeItemState800d6960);
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
   (0x800d6b08, decodeItemState800d6b08)].

(* This is the existing guarded interface, specialized to the table. *)
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
