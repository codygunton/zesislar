Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Contracts.DecodeItemSelected.

Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Proofs.DecodeItem.Composition.CompleteFamily.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6974Conditional.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemBlockTable_complete_family_native6974 `{!islaG Sigma} `{!threadG}
  (Hnative : forall (args : DecodeItemArgs) (frameBytes : list byte)
      (inputPrefix : byte) (rest : list byte),
    instr_pre 0x800d697c
      (∃ (successor_frameBytes : list byte) (successor_x13 : bv 64)
         (successor_inputPrefix : byte) (successor_rest : list byte),
        decodeItemEntryAt800d697c args successor_frameBytes successor_x13
          successor_inputPrefix successor_rest) -∗
    instr_pre 0x800d69a4
      (∃ (successor_frameBytes : list byte) (successor_x13 : bv 64)
         (successor_inputPrefix : byte) (successor_rest : list byte),
        decodeItemEntryAt800d69a4 args successor_frameBytes successor_x13
          successor_inputPrefix successor_rest) -∗
    decodeItemSelectedCode -∗ instr_body 0x800d6974
      (decodeItemEntryAt800d6974 args frameBytes inputPrefix rest ∗ True))
  (pending800d6960 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6960 decodeItemState800d6960)
  (pending800d697c :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d697c decodeItemState800d697c)
  (pending800d698c :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d698c decodeItemState800d698c)
  (pending800d69b0 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69b0 decodeItemState800d69b0)
  (pending800d69e8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69e8 decodeItemState800d69e8)
  (pending800d6a08 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a08 decodeItemState800d6a08)
  (pending800d6a24 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a24 decodeItemState800d6a24)
  (pending800d6a38 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a38 decodeItemState800d6a38)
  (pending800d6a40 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a40 decodeItemState800d6a40)
  (pending800d6a78 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a78 decodeItemState800d6a78)
  (pending800d6aa8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6aa8 decodeItemState800d6aa8)
  (pending800d6ac4 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ac4 decodeItemState800d6ac4)
  (pending800d6ad8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ad8 decodeItemState800d6ad8)
  (pending800d6ae0 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ae0 decodeItemState800d6ae0)
  (pending800d6b08 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6b08 decodeItemState800d6b08)
  : □ decodeItemSelectedCode -∗ block_table_pre decodeItemBlockTable.
Proof.
  exact (decodeItemBlockTable_complete_family pending800d6960 (decodeItemSlotBody800d6974Conditional Hnative) pending800d697c pending800d698c pending800d69b0 pending800d69e8 pending800d6a08 pending800d6a24 pending800d6a38 pending800d6a40 pending800d6a78 pending800d6aa8 pending800d6ac4 pending800d6ad8 pending800d6ae0 pending800d6b08).
Qed.
Print Assumptions decodeItemBlockTable_complete_family_native6974.
