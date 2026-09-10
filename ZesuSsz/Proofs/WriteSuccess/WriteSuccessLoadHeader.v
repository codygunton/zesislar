Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderValueTransactions.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoadBlockAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoadBlockCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoadBlockWithFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueTransactionsEntry.

Import ListNotations.

Definition writeSuccessLoadHeaderExtraRegisters :
    list (reg_kind * valu_shape) := [
  (KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)
].

Definition writeSuccessLoadHeaderResidual
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) : iProp Sigma :=
  (reg_col writeSuccessLoadHeaderExtraRegisters ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ sourceBytes ∗
   (bv_unsigned sp + 1032) ↦ₘ? 864 ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
   base ↦ₘ∗ transactionBytes ∗
   writeSuccessTransactionsOwn transactions ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions transactionBytes tail
       (writeSuccessValueTransactionsContinuation values payload P)) ∗
   writeSuccessTransactionsInvariant sp base transactions [] transactions
     transactionBytes [] transactionBytes ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeSuccessHeaderEvents sp
       (writeSuccessValueEvents sp values
         (writeSuccessTransactionsEvents sp transactions tail))) ∗
   ⌜length sourceBytes = 720%nat⌝ ∗
   ⌜bytes_of_u64s values = take 592 sourceBytes⌝ ∗
   ⌜length values = 74%nat⌝ ∗
   ⌜bv_unsigned (writeSuccessValueWord values 5) = length payload⌝ ∗
   ⌜writeSuccessValueWord values 7 = Z_to_bv 64 base⌝ ∗
   ⌜writeSuccessValueWord values 8 =
      Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Definition writeSuccessLoadHeaderSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
  (transactionBytes : list (bv 8)) : iProp Sigma :=
  (∃ (decoded : bv 64) (b10 b11 : bv 64) (loaded : list (bv 64))
      (s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64),
    writeSuccessLoadRegisterResources sp decoded b10 b11
      [RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4;
       RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8;
       RVal_Bits s9; RVal_Bits s10; RVal_Bits s11] ∗
    (bv_unsigned decoded + 720) ↦ₘ∗ loaded ∗
    bv_unsigned sp ↦ₘ? 312 ∗
    ⌜length loaded = 16%nat⌝ ∗
    ⌜bv_unsigned decoded `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned decoded + 720⌝ ∗
    ⌜bv_unsigned decoded + 848 < 0x40000000⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp⌝ ∗
    ⌜bv_unsigned sp + 312 < 0x40000000⌝ ∗
    writeSuccessLoadHeaderResidual P sp sourceBytes values payload tail base
      transactions transactionBytes)%I.

Global Instance : LithiumUnfold (@writeSuccessLoadHeaderResidual) := I.
Global Instance : LithiumUnfold (@writeSuccessLoadHeaderSpec) := I.

Lemma write_success_exact_register_to_bits
    `{!islaG Sigma} `{!threadG} (register : string) (value : bv 64) :
  (∃ actual : valu,
    ⌜valu_has_shape actual (ExactShape (RVal_Bits value))⌝ ∗
    KindReg register ↦ᵣₖ actual) -∗
  (∃ actual : valu,
    ⌜valu_has_shape actual (BitsShape 64)⌝ ∗ KindReg register ↦ᵣₖ actual).
Proof.
  iIntros "Hregister".
  iDestruct "Hregister" as (actual Hshape) "Hregister".
  cbn in Hshape. subst actual.
  iExists (RVal_Bits value). iFrame.
  iPureIntro. done.
Qed.

Lemma write_success_load_stack_to_header_gaps
    `{!islaG Sigma} (sp : bv 64) (loaded : list (bv 64)) :
  bv_unsigned sp ↦ₘ? 8 -∗
  writeSuccessLoadBlockStack sp loaded -∗
  (bv_unsigned sp + 104) ↦ₘ? 176 -∗
  bv_unsigned sp ↦ₘ? 104 ∗
  (bv_unsigned sp + 104) ↦ₘ? 16 ∗
  (bv_unsigned sp + 120) ↦ₘ? 192.
Proof.
  iIntros "Hgap0 Hstack Hgap176".
  iEval (unfold writeSuccessLoadBlockStack) in "Hstack".
  iDestruct "Hstack" as
    "(H24 & H16 & H40 & H32 & H56 & H48 & H64 & H72 & H8 & H80 &
      H296 & H304 & H280 & H288 & H96 & H88)".
  iDestruct (mem_mapsto_uninit_split 16 with "Hgap176") as
    "[Hfield Hgap160]"; [lia |].
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H8") as "H8u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H16") as "H16u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H24") as "H24u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H32") as "H32u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H40") as "H40u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H48") as "H48u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H56") as "H56u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H64") as "H64u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H72") as "H72u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H80") as "H80u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H88") as "H88u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H96") as "H96u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H280") as "H280u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H288") as "H288u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H296") as "H296u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H304") as "H304u".
  iAssert (bv_unsigned sp ↦ₘ? 104)%I with
    "[Hgap0 H8u H16u H24u H32u H40u H48u H56u H64u H72u H80u H88u H96u]"
    as "Hlower".
  { iApply (mem_mapsto_uninit_combine 8 with
      "[Hgap0] [H8u H16u H24u H32u H40u H48u H56u H64u H72u H80u H88u H96u]");
      [lia | iExact "Hgap0" |].
    replace (bv_unsigned sp + 8) with (bv_unsigned sp + 8) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H8u] [H16u H24u H32u H40u H48u H56u H64u H72u H80u H88u H96u]");
      [lia | iExact "H8u" |].
    replace (bv_unsigned sp + 8 + 8) with (bv_unsigned sp + 16) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H16u] [H24u H32u H40u H48u H56u H64u H72u H80u H88u H96u]");
      [lia | iExact "H16u" |].
    replace (bv_unsigned sp + 16 + 8) with (bv_unsigned sp + 24) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H24u] [H32u H40u H48u H56u H64u H72u H80u H88u H96u]");
      [lia | iExact "H24u" |].
    replace (bv_unsigned sp + 24 + 8) with (bv_unsigned sp + 32) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H32u] [H40u H48u H56u H64u H72u H80u H88u H96u]");
      [lia | iExact "H32u" |].
    replace (bv_unsigned sp + 32 + 8) with (bv_unsigned sp + 40) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H40u] [H48u H56u H64u H72u H80u H88u H96u]");
      [lia | iExact "H40u" |].
    replace (bv_unsigned sp + 40 + 8) with (bv_unsigned sp + 48) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H48u] [H56u H64u H72u H80u H88u H96u]");
      [lia | iExact "H48u" |].
    replace (bv_unsigned sp + 48 + 8) with (bv_unsigned sp + 56) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H56u] [H64u H72u H80u H88u H96u]");
      [lia | iExact "H56u" |].
    replace (bv_unsigned sp + 56 + 8) with (bv_unsigned sp + 64) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H64u] [H72u H80u H88u H96u]");
      [lia | iExact "H64u" |].
    replace (bv_unsigned sp + 64 + 8) with (bv_unsigned sp + 72) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H72u] [H80u H88u H96u]"); [lia | iExact "H72u" |].
    replace (bv_unsigned sp + 72 + 8) with (bv_unsigned sp + 80) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H80u] [H88u H96u]"); [lia | iExact "H80u" |].
    replace (bv_unsigned sp + 80 + 8) with (bv_unsigned sp + 88) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H88u] [H96u]"); [lia | iExact "H88u" |].
    replace (bv_unsigned sp + 88 + 8) with (bv_unsigned sp + 96) by lia.
    iExact "H96u". }
  have HgapAddress : bv_unsigned sp + 104 + 16 = bv_unsigned sp + 120 by lia.
  have HgapLength : 176 - 16 = 160 by lia.
  iEval (rewrite HgapAddress HgapLength) in "Hgap160".
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 192)%I with
    "[Hgap160 H280u H288u H296u H304u]" as "Hupper".
  { iApply (mem_mapsto_uninit_combine 160 with
      "[Hgap160] [H280u H288u H296u H304u]");
      [lia | iExact "Hgap160" |].
    replace (bv_unsigned sp + 120 + 160) with (bv_unsigned sp + 280) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H280u] [H288u H296u H304u]"); [lia | iExact "H280u" |].
    replace (bv_unsigned sp + 280 + 8) with (bv_unsigned sp + 288) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H288u] [H296u H304u]"); [lia | iExact "H288u" |].
    replace (bv_unsigned sp + 288 + 8) with (bv_unsigned sp + 296) by lia.
    iApply (mem_mapsto_uninit_combine 8 with
      "[H296u] [H304u]"); [lia | iExact "H296u" |].
    replace (bv_unsigned sp + 296 + 8) with (bv_unsigned sp + 304) by lia.
    iExact "H304u". }
  iFrame.
Qed.

Lemma write_success_load_header
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x14f04
    (writeSuccessTransactionsLoopSpec
      (writeSuccessValueTransactionsContinuation values payload P)) -∗
  instr_body 0x14d80
    (writeSuccessLoadHeaderSpec P sp sourceBytes values payload tail base
      transactions transactionBytes).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #Hbytes #Hint #Hloop".
  iPoseProof (write_success_header_value_transactions P sp sourceBytes values
    payload tail base transactions transactionBytes with
    "Hlookup Hcode Hmemcpy Houtput Hbytes Hint Hloop") as "Hheader".
  iAssert (□ instr_pre 0x14e00
    (writeSuccessHeaderValueTransactionsSpec P sp sourceBytes values payload
      tail base transactions transactionBytes))%I as "#HheaderPre".
  { iModIntro. iApply instr_pre_to_body. iNext. iExact "Hheader". }
  iPoseProof (write_success_load_adapter_with_frame with "Hcode") as "Hload".
  iApply (instr_pre_wand 0x14d80 0x14d80 false false with "Hload");
    [done | done |].
  iIntros "Hentry".
  iEval (rewrite /writeSuccessLoadHeaderSpec) in "Hentry".
  iDestruct "Hentry" as
    (decoded b10 b11 loaded s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    "(Hregs & Hloaded & Hstack & %HloadedLength & %HdecodedAlign &
      %HdecodedMin & %HdecodedMax & %HspAlign & %HspMin & %HspMax & Hres)".
  iEval (rewrite /writeSuccessLoadHeaderResidual) in "Hres".
  iDestruct "Hres" as
    "(Hextra & Hlower & Hsource & Hdestination & Hpayload & Harray & Hown &
      Hexit & Hinvariant & Hmmio & Htrace & %HsourceLength & %HvaluesBytes &
      %HvaluesLength & %HpayloadLength & %HbaseEq & %HcountEq & %Halign16 &
      %Halign8 & %HlowerBound & %HupperBound & HP & _)".
  iAssert (instr_pre 0x14e00
      (writeSuccessLoadTerminalWithFrame sp decoded loaded
        [RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4;
         RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8;
         RVal_Bits s9; RVal_Bits s10; RVal_Bits s11]))%I
    with "[HheaderPre Hextra Hlower Hsource Hdestination Hpayload Harray Hown
      Hexit Hinvariant Hmmio Htrace HP]" as "Hret".
  { iApply (instr_pre_wand 0x14e00 0x14e00 true true with "HheaderPre");
      [done | done |].
    iIntros "Hterminal".
    iEval (rewrite /writeSuccessLoadTerminalWithFrame) in "Hterminal".
    iDestruct "Hterminal" as
      "(Hsys & Hresult & H2 & H8 & Hloaded & Hstack & Hgap0 & Hgap176 &
        Hframe & _)".
    iPoseProof (write_success_load_stack_to_header_gaps sp loaded with
      "Hgap0 Hstack Hgap176") as "(Hgap104 & Hfield & Hgap192)".
    iEval (rewrite /writeSuccessHeaderValueTransactionsSpec).
    iFrame "Hsys H2 Hfield Hsource Hdestination Hmmio Htrace".
    iEval (rewrite /writeSuccessHeaderValueProviderResources).
    iFrame "Hlower Hgap104 Hgap192 Hpayload Harray Hown Hexit Hinvariant HP".
    repeat iSplit; try iPureIntro; try assumption.
    iDestruct "Hframe" as "[Hcaller Hsaved]".
    iEval (rewrite /writeSuccessLoadBlockResultRegisters
      !reg_col_cons reg_col_nil) in "Hresult".
    iEval (rewrite /writeSuccessLoadCallerFrame
      /writeSuccessLoadCallerRegShapes /writeSuccessLoadCallerRegisters
      !reg_col_cons reg_col_nil) in "Hcaller".
    iEval (rewrite /writeSuccessLoadSavedRegShapes
      /writeSuccessLoadSavedRegisters !reg_col_cons reg_col_nil) in "Hsaved".
    iEval (rewrite /writeSuccessLoadHeaderExtraRegisters
      !reg_col_cons reg_col_nil) in "Hextra".
    iEval (rewrite /writeSuccessHeaderRegShapes /writeSuccessHeaderRegisters
      !reg_col_cons reg_col_nil).
    iDestruct "Hcaller" as
      "(H1c & H15c & H16c & H17c & H5c & H6c & H7c & H28c & H29c &
        H30c & H31c & _)".
    iDestruct "Hextra" as "(H3c & H4c & _)".
    iDestruct "Hresult" as "(H10e & H11e & H12e & H13e & H14e & _)".
    iDestruct "Hsaved" as
      "(H9e & H18e & H19e & H20e & H21e & H22e & H23e & H24e & H25e &
        H26e & H27e & _)".
    iPoseProof (write_success_exact_register_to_bits with "H9e") as "H9c".
    iPoseProof (write_success_exact_register_to_bits with "H10e") as "H10c".
    iPoseProof (write_success_exact_register_to_bits with "H11e") as "H11c".
    iPoseProof (write_success_exact_register_to_bits with "H12e") as "H12c".
    iPoseProof (write_success_exact_register_to_bits with "H13e") as "H13c".
    iPoseProof (write_success_exact_register_to_bits with "H14e") as "H14c".
    iPoseProof (write_success_exact_register_to_bits with "H18e") as "H18c".
    iPoseProof (write_success_exact_register_to_bits with "H19e") as "H19c".
    iPoseProof (write_success_exact_register_to_bits with "H20e") as "H20c".
    iPoseProof (write_success_exact_register_to_bits with "H21e") as "H21c".
    iPoseProof (write_success_exact_register_to_bits with "H22e") as "H22c".
    iPoseProof (write_success_exact_register_to_bits with "H23e") as "H23c".
    iPoseProof (write_success_exact_register_to_bits with "H24e") as "H24c".
    iPoseProof (write_success_exact_register_to_bits with "H25e") as "H25c".
    iPoseProof (write_success_exact_register_to_bits with "H26e") as "H26c".
    iPoseProof (write_success_exact_register_to_bits with "H27e") as "H27c".
    iFrame "H1c H3c H4c H5c H6c H7c H15c H16c H17c H28c H29c H30c H31c".
    iFrame "H9c H10c H11c H12c H13c H14c H18c H19c H20c H21c H22c
      H23c H24c H25c H26c H27c".
    iExists (RVal_Bits decoded). iFrame "H8".
    iPureIntro. done. }
  iEval (rewrite /writeSuccessLoadAdapterWithFrameSpec
    /writeSuccessLoadMemoryWithFrame).
  iExists sp, decoded, b10, b11, loaded,
    [RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4;
     RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8;
     RVal_Bits s9; RVal_Bits s10; RVal_Bits s11].
  iFrame.
  repeat iSplit; try iPureIntro; try assumption.
Qed.
