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

Lemma decodeItemSlotBody800d6a24Conditional `{!islaG Sigma} `{!threadG}
  (Hnative : forall (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6a38 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6a24 (∃ (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24 (args) (successor_inputPrefix) (successor_rest))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a24
    (decodeItemEntryAt800d6a24 args inputPrefix rest ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6a24 decodeItemState800d6a24.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6a38
    decodeItemState800d6a38 with "Htable") as "#Hexit".
  { by apply elem_of_list_lookup_2 with 13%nat. }
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6a24
    decodeItemState800d6a24 with "Htable") as "#Hbackedge".
  { by apply elem_of_list_lookup_2 with 12%nat. }
  iPoseProof (Hnative args inputPrefix rest with "[] [] Hcode") as "Hbody".
  { iApply (instr_pre_wand with "Hexit []"); [done|done|].
    iIntros "(%nextN & %nextStart & %nextLength & %nextFrame & %nextLoaded & %nextPrefix & %nextRest & Hnext)".
    iExists args, nextN, nextStart, nextLength, nextFrame, nextLoaded, nextPrefix, nextRest.
    iExact "Hnext". }
  { iApply (instr_pre_wand with "Hbackedge []"); [done|done|].
    iIntros "(%nextPrefix & %nextRest & Hnext)".
    iExists args, nextPrefix, nextRest. iExact "Hnext". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply ("Hbody" with "[Hentry]"). iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d6a24Conditional.
