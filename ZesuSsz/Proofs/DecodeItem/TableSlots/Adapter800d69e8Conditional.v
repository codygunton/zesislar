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

Lemma decodeItemSlotBody800d69e8Conditional `{!islaG Sigma} `{!threadG}
  (Hnative : forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d698c (∃ (successor_locals : DecodeItemReturnLocals) (successor_pointerBytes : list byte) (successor_lengthBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_isLiteral : bool), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (successor_locals) (successor_pointerBytes) (successor_lengthBytes) (successor_inputPrefix) (successor_rest) (successor_isLiteral))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69e8
    (decodeItemEntryAt800d69e8 args frameBytes x13 inputPrefix rest ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d69e8 decodeItemState800d69e8.
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
    iIntros "(%nextLocals & %nextPointer & %nextLength & %nextPrefix & %nextRest & %nextLiteral & HnextEntry)".
    iExists args, nextLocals, nextPointer, nextLength, nextPrefix, nextRest, nextLiteral.
    iExact "HnextEntry". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply ("Hbody" with "[Hentry]"). iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d69e8Conditional.
