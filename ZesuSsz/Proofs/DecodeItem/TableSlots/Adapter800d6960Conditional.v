Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
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

Lemma decodeItemSlotBody800d6960Conditional `{!islaG Sigma} `{!threadG}
  (Hnative : forall (returnAddress : Z) (args : DecodeItemArgs),
  instr_pre 0x800d6974 (∃ (successor_frameBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6974 (args) (successor_frameBytes) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Generated.DecodeItem.Entries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6960
    (decodeItemEntryAt800d6960 returnAddress args ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6960 decodeItemState800d6960.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%returnAddress & %args & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6974
    decodeItemState800d6974 with "Htable") as "#Hnext".
  { by apply elem_of_list_lookup_2 with 1%nat. }
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6ae0
    decodeItemState800d6ae0 with "Htable") as "#Herror".
  { by apply elem_of_list_lookup_2 with 22%nat. }
  iPoseProof (Hnative returnAddress args with "[] [] Hcode") as "Hbody".
  { iApply (instr_pre_wand with "Hnext []"); [done|done|].
    iIntros "(%frameBytes & %inputPrefix & %rest & HnextEntry)".
    iExists args, frameBytes, inputPrefix, rest. iExact "HnextEntry". }
  { iApply (instr_pre_wand with "Herror []"); [done|done|].
    iIntros "(%locals & HerrorEntry)".
    iExists args, locals. iExact "HerrorEntry". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply ("Hbody" with "[Hentry]"). iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d6960Conditional.
