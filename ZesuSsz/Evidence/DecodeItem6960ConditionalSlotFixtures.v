Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6960Conditional.

Section fixtures.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (returnAddress : Z) (args : DecodeItemArgs),
  instr_pre 0x800d6974 (∃ (successor_frameBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974 (args) (successor_frameBytes) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6960
    (decodeItemEntryAt800d6960 returnAddress args ∗ True)).
Check (decodeItemSlotBody800d6960Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6960 decodeItemState800d6960).
Fail Check (decodeItemSlotBody800d6960Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6960 decodeItemState800d6960).
End fixtures.
Print Assumptions decodeItemSlotBody800d6960Conditional.
