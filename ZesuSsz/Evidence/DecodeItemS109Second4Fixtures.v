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

Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a38Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a40Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a78Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ad8Conditional.

Section fixture6a38.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6a40 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_headerLength : Z) (successor_payloadLength : Z), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40 (args) (successor_locals) (successor_inputPrefix) (successor_rest) (successor_headerLength) (successor_payloadLength))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a38
    (decodeItemEntryAt800d6a38 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d6a38Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a38 decodeItemState800d6a38).
Fail Check (decodeItemSlotBody800d6a38Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a38 decodeItemState800d6a38).
End fixture6a38.
Print Assumptions decodeItemSlotBody800d6a38Conditional.

Section fixture6a40.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z),
  decodeItemSelectedCode -∗
  instr_body 0x800d6a40
    (decodeItemEntryAt800d6a40 args locals inputPrefix rest headerLength payloadLength ∗ True)).
Check (decodeItemSlotBody800d6a40Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a40 decodeItemState800d6a40).
Fail Check (decodeItemSlotBody800d6a40Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a40 decodeItemState800d6a40).
End fixture6a40.
Print Assumptions decodeItemSlotBody800d6a40Conditional.

Section fixture6a78.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d6a78
    (decodeItemEntryAt800d6a78 args locals inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d6a78Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a78 decodeItemState800d6a78).
Fail Check (decodeItemSlotBody800d6a78Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a78 decodeItemState800d6a78).
End fixture6a78.
Print Assumptions decodeItemSlotBody800d6a78Conditional.

Section fixture6ad8.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  instr_pre 0x800d6b08 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_headerLength : Z) (successor_payloadLength : Z), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08 (args) (successor_locals) (successor_inputPrefix) (successor_rest) (successor_headerLength) (successor_payloadLength))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ad8
    (decodeItemEntryAt800d6ad8 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest ∗ True)).
Check (decodeItemSlotBody800d6ad8Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ad8 decodeItemState800d6ad8).
Fail Check (decodeItemSlotBody800d6ad8Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ad8 decodeItemState800d6ad8).
End fixture6ad8.
Print Assumptions decodeItemSlotBody800d6ad8Conditional.
