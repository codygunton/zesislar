Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Block800d6a14.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemSlotBody800d6a14 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a14 decodeItemState800d6a14.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %n & %payloadStart & %lengthBytes & %frameBytes & %oldAcc & %oldCursor & %loaded & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (block_table_pre_lookup decodeItemBlockTable 0x800d6a24 decodeItemState800d6a24
    with "Htable") as "#Hslot800d6a24".
  { by apply elem_of_list_lookup_2 with 12%nat. }
  iPoseProof (Block800d6a14.DesignedBoundary_800d6a14 args n payloadStart lengthBytes frameBytes oldAcc oldCursor loaded inputPrefix rest with "[] Hcode") as "Hnative".
  { iApply (instr_pre_wand with "Hslot800d6a24 []"); [done|done|].
    iIntros "(%successor_inputPrefix & %successor_rest & Hsuccessor)".
    iExists args, successor_inputPrefix, successor_rest.
    iExact "Hsuccessor". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hnative".
  iApply ("Hnative" with "[Hentry]").
  rewrite /Block800d6a14.DesignedEntry_800d6a14.
  iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d6a14.
