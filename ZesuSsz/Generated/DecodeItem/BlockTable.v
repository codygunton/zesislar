Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import lithium.lvar.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
Import ListNotations.
Local Open Scope Z_scope.

(* Generated resource wiring. No block-body proof is supplied. *)
(* Source: ZesuSsz/Automation/EntryIntro.v; SHA-256: 2e212eb5cc73c578b946a3e06c00827e268ddb3e938682ee4e6f5cc5ebd519b9. *)
(* Source: ZesuSsz/Automation/FactRegistry.v; SHA-256: d80aa53c39eeeb0bffff6d08f2e99737bf68e287059337945a339a3e7fb17579. *)
(* Source: ZesuSsz/Compliance/DecodeItemBranchGuardFacts.v; SHA-256: 7a7daa02f4516a33a9ca00724d0b5cc0f993173012a3a5962bb2b7b3a26b419c. *)
(* Source: ZesuSsz/Compliance/DecodeItemCompletedFoldFacts.v; SHA-256: 2b131dc937232c6374fd19a48ea24ec963ee636a3c0c601f155bc2c329f0c96a. *)
(* Source: ZesuSsz/Compliance/DecodeItemCorrectedWitnessSelections.v; SHA-256: 05cc674c44f798c454f1d9e23d37412fde9438d666908e44ca2a98457475caf5. *)
(* Source: ZesuSsz/Compliance/DecodeItemDataRegistrations.v; SHA-256: e8ac3680b9ef7647a0196f0494b1608e017c9a72256f295677728ed31e9bf647. *)
(* Source: ZesuSsz/Compliance/DecodeItemDataWitnessFacts.v; SHA-256: 5e7cd8b75c656c76a4d4f844169689168fa2daef9c6264c19f0db135ecfdc6ca. *)
(* Source: ZesuSsz/Compliance/DecodeItemEntryByteIndexFacts.v; SHA-256: 8409339748f5a2be73e385242154bce842ba8c466bda2f3ed625478fcb436bb9. *)
(* Source: ZesuSsz/Compliance/DecodeItemEntryGuardFacts.v; SHA-256: df511fc887a5d1eb46bdeb71e35e7cfa4b80003a7d9cae3ccb16ca48d46fc5eb. *)
(* Source: ZesuSsz/Compliance/DecodeItemEntryIntroductions.v; SHA-256: f17ca99f236502cce858eead20ef691af2a98abffcd36a961f6bf171ee7f90aa. *)
(* Source: ZesuSsz/Compliance/DecodeItemFoldExitFacts.v; SHA-256: 9d89aac84ba047be03a22d1e9219f70d8c874190eec05a9e1918ce5c82d642e4. *)
(* Source: ZesuSsz/Compliance/DecodeItemFoldRejectionFacts.v; SHA-256: d59450a91a32744178cd6ff279c922143a49cb78e2911f2d6ef88959ad5677b9. *)
(* Source: ZesuSsz/Compliance/DecodeItemFoldZeroFacts.v; SHA-256: 7d70400d781b7e57b3c055f480bb25be311b77c163465159ee7800bccaba3329. *)
(* Source: ZesuSsz/Compliance/DecodeItemHeaderWitnessFacts.v; SHA-256: fe9612e88576de35cf2b003b036a3853b9141974c2e785ca6492e7114c1a1d14. *)
(* Source: ZesuSsz/Compliance/DecodeItemInitializationPureFacts.v; SHA-256: aa44528a44e4b822be82b2873e0be5c4dee85d5aeed45e3f4c48f79aabe8a8fc. *)
(* Source: ZesuSsz/Compliance/DecodeItemInputHeadWordFacts.v; SHA-256: 1ea98710f86f2f25597cb55747859f2823a8d446a1bf9901b57d93f1a58dcdfe. *)
(* Source: ZesuSsz/Compliance/DecodeItemLoadedEntryFacts.v; SHA-256: c7a97e0a0f41eb3dc02b83175c7d990526ddff4f8951641604472dc02dd5c10d. *)
(* Source: ZesuSsz/Compliance/DecodeItemOutputBaseWitnessFacts.v; SHA-256: 48871704304b9066a327e6621197bfd6a800f73eeb06976d4bbc44dd2d9a2a49. *)
(* Source: ZesuSsz/Compliance/DecodeItemRawOutputFacts.v; SHA-256: 929943837cc0be7ed21229be7b2e6278d36d20455d8fe3a93a5711cf0bfb327b. *)
(* Source: ZesuSsz/Compliance/DecodeItemS40GuardFacts.v; SHA-256: 5358a97cf74fb1f7280226333c4fd58bbafe2c1e70799e8c2aa0ff33b7e05932. *)
(* Source: ZesuSsz/Compliance/DecodeItemSavedFrameWitnesses.v; SHA-256: 235553259498fc159ae74ddc605abeb671d72f4221d01751069570eb4a59439d. *)
(* Source: ZesuSsz/Contracts/AbiBytes.v; SHA-256: 007990c44de0b1d546b3fdcd39a828d25cfb24b4a56bdb6891cff3e74323470c. *)
(* Source: ZesuSsz/Contracts/DecodeItemBranchEntries.v; SHA-256: 85a6a567952243f919c2f170cc3bebca6eeb60d14399fb73de8af5a53e9956e0. *)
(* Source: ZesuSsz/Contracts/DecodeItemCompositional.v; SHA-256: 50d8c05339ffe8a09838bc03d61bf9edb424494b75451d249a531e79da93a426. *)
(* Source: ZesuSsz/Contracts/DecodeItemErrorBranch.v; SHA-256: 08ab01e045cc08e6eb5cceff9e542ed53ce1fd1e34fcd9b4a50c8ba324e83ee7. *)
(* Source: ZesuSsz/Contracts/DecodeItemReturnFacts.v; SHA-256: 9da33c0898953f7ff5f270dc6e1f66681f4de045c7bb774b7701676399da1cf5. *)
(* Source: ZesuSsz/Contracts/DecodeItemSelected.v; SHA-256: a8d22f12124a5c2eace1696bb13de3e774caa0e1b2a354819c03bffec26fe804. *)
(* Source: ZesuSsz/Contracts/Level1.v; SHA-256: 45e31b086c53807d6887a91578033c2c9ffdd1d55000631f063018a6f61e9d4f. *)
(* Source: ZesuSsz/Contracts/NextUint64Selected.v; SHA-256: 895a07a3a322537d848aa1e190515e5163e3a4e50edd2f7d241358b2f7766640. *)
(* Source: ZesuSsz/Contracts/ParentHeaderLevel1.v; SHA-256: 7d665aa12d4c32fbb08f1e41421744501a2ca8d0c2dae8c3870405da75a78ba6. *)
(* Source: ZesuSsz/Contracts/ParentHeaderMemcpyService.v; SHA-256: 77248046b593e864631350b0092743d3ccbf5a5fe144968317adb8911f6998c8. *)
(* Source: ZesuSsz/Contracts/ParentHeaderSelected.v; SHA-256: 21c4ae10ca952f07291508caba10dcc836a78afad4260661a4ffc26acfd74f7c. *)
(* Source: ZesuSsz/Contracts/ResultImage.v; SHA-256: 25304efe309a5644c10bd39a98bcd914c42d30c51a5eeed62ba231c97e4a209d. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItem.v; SHA-256: 00fb772278173d367df71d67413b17e2631a863c1f384d763412000ac2b4b76e. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemBlockEntries.v; SHA-256: cc0c5d1d6872d48549fc0a06b9630f0a89ff942afc39db29321548e30dc055d4. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemByteFold.v; SHA-256: 6f80226eadadd5468b46aebc8c48561f54815f94c1989e465d530f6896e4237d. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemByteFoldBlocks.v; SHA-256: a504dfa090e1ec91f709ad3c3b5c7df1823dc64159b0b53960a0606a5ffe92a9. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemByteFoldSites.v; SHA-256: 8f8a64ac921387fef087cafeb68204e045dc5e40f7c2ec9d55c4475b9981bee3. *)
(* Source: ZesuSsz/Contracts/RlpDecodeItemContract.v; SHA-256: 595fab72b6fcaa0603a8bd35f5e3b4433a380493a076f2bf8d05116738355d9a. *)
(* Source: ZesuSsz/Evidence/decode_item_block_design.json; SHA-256: 476e07b7852c2c0a91124df93c6b0674334d12a265552739251925857f54e151. *)
(* Source: ZesuSsz/Evidence/generate_block_design.py; SHA-256: a1de40fde4c6b56e8342b642b4fd89d37887c81b84aad86ba1d62943b4acabed. *)
(* Source: ZesuSsz/Generated/DecodeItem/Entries.v; SHA-256: 362c58e1b20c6e0ed75d93fca8b215be6956c6a2202914975edb0bc1d05e3e32. *)
(* Source: build/stock-zisk/cfg.json; SHA-256: 22b462dafc29cc0efbb38eb0f6c6300998122dc53e29c400ebe9f6cce55308e2. *)
(* Source: build/stock-zisk/decodeItem.raw.dump; SHA-256: 309bfd72ccac295008856beb22ba83fc6834ac97c56f7591a8a1316ec7e52a2b. *)
(* Source: build/stock-zisk/inventory.json; SHA-256: b7a3cde815744ca0babedf52bf5626403f5f133bc1350f40634e5c54ff9dbe86. *)
(* Source: tools/block/check_data_only_lemmas.py; SHA-256: dd6f978329f3e9b7d48995335d207532e7ff94260d027da1867565e3a60ab87c. *)
(* Source: tools/block/entry_bindings.py; SHA-256: f68373d49d74fd715204d48189480a8eaa0f816a2438b5763c459165753bc39a. *)
(* Source: tools/block/entry_schema.py; SHA-256: 3f91d05aced7cb0eaec0b0363d073f0f6dc59bdf638a469d72abda954059a167. *)
(* Source: tools/block/function_names.py; SHA-256: 619eb4b97f110e5158e950fa84f91753210605512dd921a603c55bded6bdd5e9. *)
(* Source: tools/block/generate_table.py; SHA-256: 460d42f603b58f5cb6db8ca74ee73affebdc86bcc56306d6bd3ac517d8716ee0. *)
(* Source: tools/block/render_support.py; SHA-256: 32d7c86dbe0a8253af930f8e26f704a1a6bca5dd882947058d95ad16463044d0. *)
(* Source: tools/block/trace_registers.py; SHA-256: 0fe25ade825c1fd600f433d83a56dcc1a5ee187c7081860205f7ea383bfb405d. *)

Section decode_item_block_table.
Context `{!islaG Sigma} `{!threadG}.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6960. Body proof: pending. *)
Definition decodeItemState800d6960 : iProp Sigma :=
  (∃ (returnAddress : Z) (args : DecodeItemArgs), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6960 (returnAddress) (args))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6974. Body proof: pending. *)
Definition decodeItemState800d6974 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6974 (args) (frameBytes) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d697c. Body proof: pending. *)
Definition decodeItemState800d697c : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d697c (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d698c. Body proof: pending. *)
Definition decodeItemState800d698c : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (x11 : bv 64) (x12 : bv 64) (x13 : bv 64) (x14 : bv 64) (x15 : bv 64) (x16 : bv 64) (outputBytes : list (bv 8)) (frameBytes : list (bv 8)) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d698c (args) (x11) (x12) (x13) (x14) (x15) (x16) (outputBytes) (frameBytes) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69a4. Body proof: pending. *)
Definition decodeItemState800d69a4 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69a4 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69b0. Body proof: pending. *)
Definition decodeItemState800d69b0 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69b0 (args) (locals) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69d8. Body proof: pending. *)
Definition decodeItemState800d69d8 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69d8 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69e0. Body proof: pending. *)
Definition decodeItemState800d69e0 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69e0 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69e8. Body proof: pending. *)
Definition decodeItemState800d69e8 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d69e8 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a00. Body proof: pending. *)
Definition decodeItemState800d6a00 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a00 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a08. Body proof: pending. *)
Definition decodeItemState800d6a08 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a08 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a14. Body proof: pending. *)
Definition decodeItemState800d6a14 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list (bv 8)) (frameBytes : list (bv 8)) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a14 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a24. Body proof: pending. *)
Definition decodeItemState800d6a24 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (prefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a24 (args) (prefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a38. Body proof: pending. *)
Definition decodeItemState800d6a38 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list (bv 8)) (frameBytes : list (bv 8)) (loaded : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a38 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a40. Body proof: pending. *)
Definition decodeItemState800d6a40 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : bv 8) (rest : list (bv 8)) (headerLength : Z) (payloadLength : Z), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a40 (args) (locals) (inputPrefix) (rest) (headerLength) (payloadLength))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a64. Body proof: pending. *)
Definition decodeItemState800d6a64 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a64 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a6c. Body proof: pending. *)
Definition decodeItemState800d6a6c : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a6c (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a78. Body proof: pending. *)
Definition decodeItemState800d6a78 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a78 (args) (locals) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6aa8. Body proof: pending. *)
Definition decodeItemState800d6aa8 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (frameBytes : list (bv 8)) (x13 : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6aa8 (args) (frameBytes) (x13) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ab4. Body proof: pending. *)
Definition decodeItemState800d6ab4 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list (bv 8)) (frameBytes : list (bv 8)) (oldAcc : bv 64) (oldCursor : bv 64) (loaded : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ab4 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ac4. Body proof: pending. *)
Definition decodeItemState800d6ac4 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (prefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ac4 (args) (prefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ad8. Body proof: pending. *)
Definition decodeItemState800d6ad8 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list (bv 8)) (frameBytes : list (bv 8)) (loaded : bv 64) (inputPrefix : bv 8) (rest : list (bv 8)), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ad8 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) (inputPrefix) (rest))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ae0. Body proof: pending. *)
Definition decodeItemState800d6ae0 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ae0 (args) (locals))%I.

(* Entry: ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6b08. Body proof: pending. *)
Definition decodeItemState800d6b08 : iProp Sigma :=
  (∃ (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : bv 8) (rest : list (bv 8)) (headerLength : Z) (payloadLength : Z), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6b08 (args) (locals) (inputPrefix) (rest) (headerLength) (payloadLength))%I.

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
