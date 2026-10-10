Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6974Conditional.

Section fixtures.
Context `{!islaG Sigma} `{!threadG}.
Context (Hnative : forall (args : DecodeItemArgs) (frameBytes : list byte)
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
      (decodeItemEntryAt800d6974 args frameBytes inputPrefix rest ∗ True)).

Check (decodeItemSlotBody800d6974Conditional Hnative :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6974 decodeItemState800d6974).

Fail Check (decodeItemSlotBody800d6974Conditional :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6974 decodeItemState800d6974).
End fixtures.
Print Assumptions decodeItemSlotBody800d6974Conditional.
