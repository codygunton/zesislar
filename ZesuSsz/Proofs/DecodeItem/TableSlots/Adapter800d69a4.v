Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Block800d69a4.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemSlotBody800d69a4 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69a4 decodeItemState800d69a4.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %frameBytes & %x13 & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d69b0 decodeItemState800d69b0
    with "Htable") as "#Hslot800d69b0".
  { by apply elem_of_list_lookup_2 with 5%nat. }
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d69d8 decodeItemState800d69d8
    with "Htable") as "#Hslot800d69d8".
  { by apply elem_of_list_lookup_2 with 6%nat. }
  iPoseProof (Block800d69a4.DesignedBoundary_800d69a4 args frameBytes x13 inputPrefix rest with "[] [] Hcode") as "Hnative".
  { iApply (instr_pre_wand with "Hslot800d69b0 []"); [done|done|].
    iIntros "(%successor_locals & %successor_inputPrefix & %successor_rest & Hsuccessor)".
    iExists args, successor_locals, successor_inputPrefix, successor_rest.
    iExact "Hsuccessor". }
  { iApply (instr_pre_wand with "Hslot800d69d8 []"); [done|done|].
    iIntros "(%successor_frameBytes & %successor_x13 & %successor_inputPrefix & %successor_rest & Hsuccessor)".
    iExists args, successor_frameBytes, successor_x13, successor_inputPrefix, successor_rest.
    iExact "Hsuccessor". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hnative".
  iApply ("Hnative" with "[Hentry]").
  rewrite /Block800d69a4.DesignedEntry_800d69a4.
  iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d69a4.
