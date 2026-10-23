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

Lemma decodeItemSlotBody800d6a38Conditional `{!islaG Sigma} `{!threadG}
  (Hnative : forall (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6a40 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_headerLength : Z) (successor_payloadLength : Z), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6a40 (args) (successor_locals) (successor_inputPrefix) (successor_rest) (successor_headerLength) (successor_payloadLength))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a38
    (decodeItemEntryAt800d6a38 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6a38 decodeItemState800d6a38.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %n & %payloadStart & %lengthBytes & %frameBytes & %loaded & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6a40
    decodeItemState800d6a40 with "Htable") as "#Haccepted".
  { by apply elem_of_list_lookup_2 with 14%nat. }
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6ae0
    decodeItemState800d6ae0 with "Htable") as "#Hrejected".
  { by apply elem_of_list_lookup_2 with 22%nat. }
  iPoseProof (Hnative args n payloadStart lengthBytes frameBytes loaded inputPrefix rest with "[] [] Hcode") as "Hbody".
  { iApply (instr_pre_wand with "Haccepted []"); [done|done|].
    iIntros "(%nextLocals & %nextPrefix & %nextRest & %nextHeader & %nextPayload & Hnext)".
    iExists args, nextLocals, nextPrefix, nextRest, nextHeader, nextPayload. iExact "Hnext". }
  { iApply (instr_pre_wand with "Hrejected []"); [done|done|].
    iIntros "(%nextLocals & Hnext)". iExists args, nextLocals. iExact "Hnext". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply ("Hbody" with "[Hentry]"). iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d6a38Conditional.
