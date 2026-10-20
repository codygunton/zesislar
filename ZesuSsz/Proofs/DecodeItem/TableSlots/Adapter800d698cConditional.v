Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.

Lemma decodeItemSlotBody800d698cConditional `{!islaG Sigma} `{!threadG}
  (Hliteral : forall (args : DecodeItemArgs) (x11 x12 x13 x14 x15 x16 : bv 64) (outputBytes frameBytes : list byte) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d698c
    (decodeItemEntryAt800d698cLiteral args x11 x12 x13 x14 x15 x16 outputBytes frameBytes inputPrefix rest ∗ True))
  (Hshort : forall (args : DecodeItemArgs) (x11 x12 x13 x14 x15 x16 : bv 64) (outputBytes frameBytes : list byte) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d698c
    (decodeItemEntryAt800d698cShortString args x11 x12 x13 x14 x15 x16 outputBytes frameBytes inputPrefix rest ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d698c decodeItemState800d698c.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %x11 & %x12 & %x13 & %x14 & %x15 & %x16 & %outputBytes & %frameBytes & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iEval (unfold decodeItemEntryAt800d698c) in "Hentry".
  iDestruct "Hentry" as "[Hentry|Hentry]".
  { iPoseProof (Hliteral args x11 x12 x13 x14 x15 x16 outputBytes frameBytes inputPrefix rest with "Hcode") as "Hbody".
    iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
    iApply ("Hbody" with "[Hentry]").
    iSplitL "Hentry"; [iExact "Hentry"|done]. }
  { iPoseProof (Hshort args x11 x12 x13 x14 x15 x16 outputBytes frameBytes inputPrefix rest with "Hcode") as "Hbody".
    iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
    iApply ("Hbody" with "[Hentry]").
    iSplitL "Hentry"; [iExact "Hentry"|done]. }
Qed.
Print Assumptions decodeItemSlotBody800d698cConditional.
