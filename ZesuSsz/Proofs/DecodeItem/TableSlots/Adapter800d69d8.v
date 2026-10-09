Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Block800d69d8.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemSlotBody800d69d8 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69d8 decodeItemState800d69d8.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %frameBytes & %x13 & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d69e0 decodeItemState800d69e0
    with "Htable") as "#Hslot800d69e0".
  { by apply elem_of_list_lookup_2 with 7%nat. }
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6a00 decodeItemState800d6a00
    with "Htable") as "#Hslot800d6a00".
  { by apply elem_of_list_lookup_2 with 9%nat. }
  iPoseProof (Block800d69d8.DesignedBoundary_800d69d8 args frameBytes x13 inputPrefix rest with "[] [] Hcode") as "Hnative".
  { iApply (instr_pre_wand with "Hslot800d69e0 []"); [done|done|].
    iIntros "(%successor_frameBytes & %successor_x13 & %successor_inputPrefix & %successor_rest & Hsuccessor)".
    iExists args, successor_frameBytes, successor_x13, successor_inputPrefix, successor_rest.
    iExact "Hsuccessor". }
  { iApply (instr_pre_wand with "Hslot800d6a00 []"); [done|done|].
    iIntros "(%successor_frameBytes & %successor_x13 & %successor_inputPrefix & %successor_rest & Hsuccessor)".
    iExists args, successor_frameBytes, successor_x13, successor_inputPrefix, successor_rest.
    iExact "Hsuccessor". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hnative".
  iApply ("Hnative" with "[Hentry]").
  rewrite /Block800d69d8.DesignedEntry_800d69d8.
  iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d69d8.
