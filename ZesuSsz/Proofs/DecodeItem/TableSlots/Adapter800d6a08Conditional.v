Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
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

Lemma decodeItemSlotBody800d6a08Conditional `{!islaG Sigma} `{!threadG}
  (Hnative : forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6a14 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_oldAcc : bv 64) (successor_oldCursor : bv 64) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a14 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_oldAcc) (successor_oldCursor) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a08
    (decodeItemEntryAt800d6a08 args frameBytes x13 inputPrefix rest ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6a08 decodeItemState800d6a08.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %frameBytes & %x13 & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6a14
    decodeItemState800d6a14 with "Htable") as "#Haccepted".
  { by apply elem_of_list_lookup_2 with 11%nat. }
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6ae0
    decodeItemState800d6ae0 with "Htable") as "#Hrejected".
  { by apply elem_of_list_lookup_2 with 22%nat. }
  iPoseProof (Hnative args frameBytes x13 inputPrefix rest with "[] [] Hcode") as "Hbody".
  { iApply (instr_pre_wand with "Haccepted []"); [done|done|].
    iIntros "(%nextN & %nextStart & %nextLength & %nextFrame & %nextAcc & %nextCursor & %nextLoaded & %nextPrefix & %nextRest & Hnext)".
    iExists args, nextN, nextStart, nextLength, nextFrame, nextAcc, nextCursor, nextLoaded, nextPrefix, nextRest.
    iExact "Hnext". }
  { iApply (instr_pre_wand with "Hrejected []"); [done|done|].
    iIntros "(%nextLocals & Hnext)". iExists args, nextLocals. iExact "Hnext". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply ("Hbody" with "[Hentry]"). iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d6a08Conditional.
