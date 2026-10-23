Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
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

Lemma decodeItemSlotBody800d6974Conditional `{!islaG Sigma} `{!threadG}
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
      (decodeItemEntryAt800d6974 args frameBytes inputPrefix rest ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6974 decodeItemState800d6974.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %frameBytes & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d697c
    decodeItemState800d697c with "Htable") as "#Hlow".
  { by apply elem_of_list_lookup_2 with 2%nat. }
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d69a4
    decodeItemState800d69a4 with "Htable") as "#Hhigh".
  { by apply elem_of_list_lookup_2 with 4%nat. }
  iPoseProof (Hnative args frameBytes inputPrefix rest with "[] [] Hcode") as "Hbody".
  { iApply (instr_pre_wand with "Hlow []"); [done|done|].
    iIntros "(%nextFrame & %nextX13 & %nextPrefix & %nextRest & Hnext)".
    iExists args, nextFrame, nextX13, nextPrefix, nextRest. iExact "Hnext". }
  { iApply (instr_pre_wand with "Hhigh []"); [done|done|].
    iIntros "(%nextFrame & %nextX13 & %nextPrefix & %nextRest & Hnext)".
    iExists args, nextFrame, nextX13, nextPrefix, nextRest. iExact "Hnext". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply ("Hbody" with "[Hentry]"). iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d6974Conditional.
