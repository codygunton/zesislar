Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Block800d6a6c.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemSlotBody800d6a6c `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a6c decodeItemState800d6a6c.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %frameBytes & %x13 & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6a78 decodeItemState800d6a78
    with "Htable") as "#Hslot800d6a78".
  { by apply elem_of_list_lookup_2 with 17%nat. }
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6ae0 decodeItemState800d6ae0
    with "Htable") as "#Hslot800d6ae0".
  { by apply elem_of_list_lookup_2 with 22%nat. }
  iPoseProof (Block800d6a6c.DesignedBoundary_800d6a6c args frameBytes x13 inputPrefix rest with "[] [] Hcode") as "Hnative".
  { iApply (instr_pre_wand with "Hslot800d6a78 []"); [done|done|].
    iIntros "(%successor_locals & %successor_inputPrefix & %successor_rest & Hsuccessor)".
    iExists args, successor_locals, successor_inputPrefix, successor_rest.
    iExact "Hsuccessor". }
  { iApply (instr_pre_wand with "Hslot800d6ae0 []"); [done|done|].
    iIntros "(%successor_locals & Hsuccessor)".
    iExists args, successor_locals.
    iExact "Hsuccessor". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hnative".
  iApply ("Hnative" with "[Hentry]").
  rewrite /Block800d6a6c.DesignedEntry_800d6a6c.
  iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d6a6c.
