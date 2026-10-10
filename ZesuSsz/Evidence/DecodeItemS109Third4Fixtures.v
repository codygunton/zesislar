Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a08Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6aa8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ae0Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6b08Conditional.

Section fixture6a08.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6a14 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_oldAcc : bv 64) (successor_oldCursor : bv 64) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a14 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_oldAcc) (successor_oldCursor) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a08
    (decodeItemEntryAt800d6a08 args frameBytes x13 inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d6a08Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a08 decodeItemState800d6a08).
Fail Check (decodeItemSlotBody800d6a08Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a08 decodeItemState800d6a08).
End fixture6a08.
Print Assumptions decodeItemSlotBody800d6a08Conditional.

Section fixture6aa8.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6ab4 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_oldAcc : bv 64) (successor_oldCursor : bv 64) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ab4 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_oldAcc) (successor_oldCursor) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6aa8
    (decodeItemEntryAt800d6aa8 args frameBytes x13 inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d6aa8Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6aa8 decodeItemState800d6aa8).
Fail Check (decodeItemSlotBody800d6aa8Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6aa8 decodeItemState800d6aa8).
End fixture6aa8.
Print Assumptions decodeItemSlotBody800d6aa8Conditional.

Section fixture6ae0.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals),
  decodeItemSelectedCode -∗
  instr_body 0x800d6ae0
    (decodeItemEntryAt800d6ae0 args locals ∗ True)).
Check (decodeItemSlotBody800d6ae0Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ae0 decodeItemState800d6ae0).
Fail Check (decodeItemSlotBody800d6ae0Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ae0 decodeItemState800d6ae0).
End fixture6ae0.
Print Assumptions decodeItemSlotBody800d6ae0Conditional.

Section fixture6b08.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z),
  decodeItemSelectedCode -∗
  instr_body 0x800d6b08
    (decodeItemEntryAt800d6b08 args locals inputPrefix rest headerLength payloadLength ∗ True)).
Check (decodeItemSlotBody800d6b08Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6b08 decodeItemState800d6b08).
Fail Check (decodeItemSlotBody800d6b08Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6b08 decodeItemState800d6b08).
End fixture6b08.
Print Assumptions decodeItemSlotBody800d6b08Conditional.
