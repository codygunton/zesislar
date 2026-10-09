Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Block800d6a00.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemSlotBody800d6a00 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a00 decodeItemState800d6a00.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %frameBytes & %x13 & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6a08 decodeItemState800d6a08
    with "Htable") as "#Hslot800d6a08".
  { by apply elem_of_list_lookup_2 with 10%nat. }
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6a64 decodeItemState800d6a64
    with "Htable") as "#Hslot800d6a64".
  { by apply elem_of_list_lookup_2 with 15%nat. }
  iPoseProof (Block800d6a00.DesignedBoundary_800d6a00 args frameBytes x13 inputPrefix rest with "[] [] Hcode") as "Hnative".
  { iApply (instr_pre_wand with "Hslot800d6a08 []"); [done|done|].
    iIntros "(%successor_frameBytes & %successor_x13 & %successor_inputPrefix & %successor_rest & Hsuccessor)".
    iExists args, successor_frameBytes, successor_x13, successor_inputPrefix, successor_rest.
    iExact "Hsuccessor". }
  { iApply (instr_pre_wand with "Hslot800d6a64 []"); [done|done|].
    iIntros "(%successor_frameBytes & %successor_x13 & %successor_inputPrefix & %successor_rest & Hsuccessor)".
    iExists args, successor_frameBytes, successor_x13, successor_inputPrefix, successor_rest.
    iExact "Hsuccessor". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hnative".
  iApply ("Hnative" with "[Hentry]").
  rewrite /Block800d6a00.DesignedEntry_800d6a00.
  iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d6a00.
