Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a24Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ac4Conditional.

Section fixture6a24.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6a38 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6a24 (∃ (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24 (args) (successor_inputPrefix) (successor_rest))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a24
    (decodeItemEntryAt800d6a24 args inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d6a24Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a24 decodeItemState800d6a24).
Fail Check (decodeItemSlotBody800d6a24Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a24 decodeItemState800d6a24).
End fixture6a24.
Print Assumptions decodeItemSlotBody800d6a24Conditional.

Section fixture6ac4.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6ad8 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ad8 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ac4 (∃ (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6ac4 (args) (successor_inputPrefix) (successor_rest))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ac4
    (decodeItemEntryAt800d6ac4 args inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d6ac4Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ac4 decodeItemState800d6ac4).
Fail Check (decodeItemSlotBody800d6ac4Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ac4 decodeItemState800d6ac4).
End fixture6ac4.
Print Assumptions decodeItemSlotBody800d6ac4Conditional.
