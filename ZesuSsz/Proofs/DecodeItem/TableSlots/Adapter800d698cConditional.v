Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma decodeItemSlotBody800d698cConditional `{!islaG Sigma} `{!threadG}
  (Hnative : forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (pointerBytes : list byte) (lengthBytes : list byte) (inputPrefix : byte) (rest : list byte) (isLiteral : bool),
  decodeItemSelectedCode -∗
  instr_body 0x800d698c
    (decodeItem698cCaseResources args locals pointerBytes lengthBytes inputPrefix rest isLiteral ∗ True)) :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d698c decodeItemState800d698c.
Proof.
  iIntros "#Htable".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "(%args & %x11 & %x12 & %x13 & %x14 & %x15 & %x16 & %outputBytes & %frameBytes & %inputPrefix & %rest & Hentry)".
  iPoseProof (block_table_pre_code with "Htable") as "#Hcode".
  iEval (unfold decodeItemEntryAt800d698c) in "Hentry".
  iDestruct "Hentry" as "[Hentry|Hentry]".
  { iPoseProof (Hnative args
      {| returnA1 := x11; returnA2 := x12; returnA3 := x13;
         returnA4 := x14; returnA5 := x15; returnA6 := x16;
         returnStorage := outputBytes; returnFrame := frameBytes |}
      (word64Bytes (bv_unsigned x11)) (word64Bytes (bv_unsigned x12)) inputPrefix rest true with "Hcode") as "Hbody".
    iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
    iApply ("Hbody" with "[Hentry]").
    iSplitL "Hentry"; last done.
    iEval (unfold decodeItemEntryAt800d698cLiteral) in "Hentry".
    iDestruct "Hentry" as "[Hcore %Hfields]".
    unfold decodeItem698cCaseResources. iFrame "Hcore". iPureIntro.
    cbn [returnA1 returnA2 returnStorage].
    rewrite <- (decodeItemStoredWordBytes x11), <- (decodeItemStoredWordBytes x12) in *.
    rewrite decodeItemStoredWordValue.
    rewrite length_bv_to_little_endian; last (compute; discriminate).
    naive_solver. }
  { iPoseProof (Hnative args
      {| returnA1 := x11; returnA2 := x12; returnA3 := x13;
         returnA4 := x14; returnA5 := x15; returnA6 := x16;
         returnStorage := outputBytes; returnFrame := frameBytes |}
      (word64Bytes (bv_unsigned x11)) (word64Bytes (bv_unsigned x13)) inputPrefix rest false with "Hcode") as "Hbody".
    iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
    iApply ("Hbody" with "[Hentry]").
    iSplitL "Hentry"; last done.
    iEval (unfold decodeItemEntryAt800d698cShortString) in "Hentry".
    iDestruct "Hentry" as "[Hcore %Hfields]".
    unfold decodeItem698cCaseResources. iFrame "Hcore". iPureIntro.
    cbn [returnA1 returnA2 returnStorage].
    rewrite <- (decodeItemStoredWordBytes x11), <- (decodeItemStoredWordBytes x13) in *.
    rewrite decodeItemStoredWordValue.
    rewrite length_bv_to_little_endian; last (compute; discriminate).
    naive_solver. }

Qed.
Print Assumptions decodeItemSlotBody800d698cConditional.
