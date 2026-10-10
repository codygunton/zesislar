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

Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d697cConditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d698cConditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69b0Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e8Conditional.

Section fixture697c.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d698c (∃ (successor_locals : DecodeItemReturnLocals) (successor_pointerBytes : list byte) (successor_lengthBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_isLiteral : bool), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (successor_locals) (successor_pointerBytes) (successor_lengthBytes) (successor_inputPrefix) (successor_rest) (successor_isLiteral))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d697c
    (decodeItemEntryAt800d697c args frameBytes x13 inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d697cConditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d697c decodeItemState800d697c).
Fail Check (decodeItemSlotBody800d697cConditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d697c decodeItemState800d697c).
End fixture697c.
Print Assumptions decodeItemSlotBody800d697cConditional.

Section fixture698c.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (pointerBytes : list byte) (lengthBytes : list byte) (inputPrefix : byte) (rest : list byte) (isLiteral : bool),
  decodeItemSelectedCode -∗
  instr_body 0x800d698c
    (decodeItemEntryAt800d698c args locals pointerBytes lengthBytes inputPrefix rest isLiteral ∗ True)).
Check (decodeItemSlotBody800d698cConditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d698c decodeItemState800d698c).
Fail Check (decodeItemSlotBody800d698cConditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d698c decodeItemState800d698c).
End fixture698c.
Print Assumptions decodeItemSlotBody800d698cConditional.

Section fixture69b0.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d69b0
    (decodeItemEntryAt800d69b0 args locals inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d69b0Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69b0 decodeItemState800d69b0).
Fail Check (decodeItemSlotBody800d69b0Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69b0 decodeItemState800d69b0).
End fixture69b0.
Print Assumptions decodeItemSlotBody800d69b0Conditional.

Section fixture69e8.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d698c (∃ (successor_locals : DecodeItemReturnLocals) (successor_pointerBytes : list byte) (successor_lengthBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_isLiteral : bool), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (successor_locals) (successor_pointerBytes) (successor_lengthBytes) (successor_inputPrefix) (successor_rest) (successor_isLiteral))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69e8
    (decodeItemEntryAt800d69e8 args frameBytes x13 inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d69e8Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69e8 decodeItemState800d69e8).
Fail Check (decodeItemSlotBody800d69e8Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69e8 decodeItemState800d69e8).
End fixture69e8.
Print Assumptions decodeItemSlotBody800d69e8Conditional.
