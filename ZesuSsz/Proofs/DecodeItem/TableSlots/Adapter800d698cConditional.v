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

Lemma decodeItemSlotBody800d698cConditional `{!islaG Sigma} `{!threadG}
  (Hnative : forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (pointerBytes : list byte) (lengthBytes : list byte) (inputPrefix : byte) (rest : list byte) (isLiteral : bool),
  decodeItemSelectedCode -∗
  instr_body 0x800d698c
    (decodeItemEntryAt800d698c args locals pointerBytes lengthBytes inputPrefix rest isLiteral ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d698c decodeItemState800d698c.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %locals & %pointerBytes & %lengthBytes & %inputPrefix & %rest & %isLiteral & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iPoseProof (Hnative args locals pointerBytes lengthBytes inputPrefix rest isLiteral with "Hcode") as "Hbody".
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply ("Hbody" with "[Hentry]"). iFrame.
Qed.
Print Assumptions decodeItemSlotBody800d698cConditional.
