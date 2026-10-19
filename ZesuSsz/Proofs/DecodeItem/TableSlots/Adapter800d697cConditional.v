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

Lemma decodeItemSlotBody800d697cConditional `{!islaG Sigma} `{!threadG}
  (Hnative : forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d698c (∃ (successor_x11 successor_x12 successor_x13 successor_x14 successor_x15 successor_x16 : bv 64) (successor_outputBytes successor_frameBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698cLiteral args successor_x11 successor_x12 successor_x13 successor_x14 successor_x15 successor_x16 successor_outputBytes successor_frameBytes successor_inputPrefix successor_rest)%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d697c
    (decodeItemEntryAt800d697c args frameBytes x13 inputPrefix rest ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d697c decodeItemState800d697c.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %frameBytes & %x13 & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d698c
    decodeItemState800d698c with "Htable") as "#Hnext".
  { by apply elem_of_list_lookup_2 with 3%nat. }
  iPoseProof (Hnative args frameBytes x13 inputPrefix rest with "[] Hcode") as "Hbody".
  { iApply (instr_pre_wand with "Hnext []"); [done|done|].
    iIntros "(%nextA1 & %nextA2 & %nextA3 & %nextA4 & %nextA5 & %nextA6 & %nextStorage & %nextFrame & %nextPrefix & %nextRest & HnextEntry)".
    iExists args, nextA1, nextA2, nextA3, nextA4, nextA5, nextA6,
      nextStorage, nextFrame, nextPrefix, nextRest.
    rewrite /decodeItemEntryAt800d698c. iLeft. iExact "HnextEntry". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply ("Hbody" with "[Hentry]"). iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d697cConditional.
