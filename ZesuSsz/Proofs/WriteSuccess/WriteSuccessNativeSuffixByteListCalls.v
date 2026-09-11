Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_114 Require Import a1594c_spec.
From IslaTraces.write_success_115 Require Import a1595c_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixByteListSetups.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixScalarSetups.

Import ListNotations.

Definition writeSuccessPostByteListCallSaved : list string :=
  ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
   "x22"; "x23"; "x24"; "x25"; "x26"; "x27"].

Definition writeSuccessPost1594cCallEntrySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count pointer2 count2 : bv 64)
      (b12 b13 b14 b15 b16 b17 : bv 64)
      (saved : list valu) (items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    reg_col (zip_with (fun r v => (KindReg r, BitsShape 64))
      writeSuccessPostByteListCallSaved saved) ∗
    ⌜length saved = 12%nat⌝ ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15948) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗ "x11" ↦ᵣ RVal_Bits count ∗
    "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗
    "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
    "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗
    (bv_unsigned sp - 80) ↦ₘ? 80 ∗
    (bv_unsigned sp + 40) ↦ₘ pointer ∗
    (bv_unsigned sp + 32) ↦ₘ count ∗
    (bv_unsigned sp + 56) ↦ₘ pointer2 ∗
    (bv_unsigned sp + 48) ↦ₘ count2 ∗
    byteListItemResources (bv_unsigned pointer) items ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
        (byteListItemEvents (sp - BV 64 32)%bv items tail)) ∗
    ⌜bv_unsigned count = length items⌝ ∗
    ⌜length items < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (length items) < 0x40000000⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 80 /\
      bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 56 < 0x40000000⌝ ∗ P)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPost1594cCallEntrySpec) := I.

Lemma write_success_post_1594c_byte_lists_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  byteListsCode -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_pre 0x1595c (writeSuccessPost1595cSetupSpec P) -∗
  instr_body 0x15950 (writeSuccessPost15950SetupSpec P) -∗
  instr_body 0x1594c (writeSuccessPost1594cCallEntrySpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode HbyteLists #Hint #Hbytes Hcontinuation Hnext".
  iPoseProof (write_success_byte_lists with "HbyteLists Hint Hbytes")
    as "HcalleeBody".
  iAssert (instr_pre 0x15c10 zesuEncoderByteListsCallSpec)%I
    with "[HcalleeBody]" as "Hcallee".
  { iApply instr_pre_to_body. iNext. iExact "HcalleeBody". }
  iPoseProof "Hlookup" as "#Hlookup1594c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1594c".
  iPoseProof ("Hlookup1594c" $! 0x1594c with "[]") as "#Hinstr1594c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1594c.
    done. }
  iPoseProof (IslaTraces.write_success_114.a1594c_spec.a1594c_spec
    0x1594c with "Hinstr1594c") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessPost1594cCallEntrySpec) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer count pointer2 count2 b12 b13 b14 b15 b16 b17 saved items tail)
    "(Hsys & Htmp & Hsaved & %HsavedLength & H1 & H2 & H10 & H11 &
      H12 & H13 & H14 & H15 & H16 & H17 & Hstack80 & Hstack40 & Hstack32 &
      Hstack56 & Hstack48 & Hitems & Hmmio & Htrace & %Hcount &
      %HitemsLength & %HfirstAlign & %HfirstLower & %HfirstUpper &
      %HspAlign & %HspBounds & %HspUpper56 & HP)".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x15948). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x15948) + BV 64 712)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15c10
    by bv_solve.
  rewrite Htarget.
  iEval (rewrite -instr_pre'_eq) in "Hcallee".
  iPoseProof (instr_pre_wand 0x15c10 0x15c10 true true
    with "Hcallee") as "Htarget"; [done | reflexivity |].
  iApply "Htarget".
  iIntros "(HsysCall & Hret & _ )".
  iEval (unfold zesuEncoderByteListsCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x15950).
  destruct saved as [|v8 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v9 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v18 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v19 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v20 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v21 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v22 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v23 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v24 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v25 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v26 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v27 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|vrest rest]; cbn in HsavedLength; try lia.
  iEval (unfold writeSuccessPostByteListCallSaved; cbn) in "Hsaved".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 &
      H26 & H27 & _)".
  iDestruct "H8" as (r8) "(%Hr8 & H8)".
  iDestruct "H9" as (r9) "(%Hr9 & H9)".
  iDestruct "H18" as (r18) "(%Hr18 & H18)".
  iDestruct "H19" as (r19) "(%Hr19 & H19)".
  iDestruct "H20" as (r20) "(%Hr20 & H20)".
  iDestruct "H21" as (r21) "(%Hr21 & H21)".
  iDestruct "H22" as (r22) "(%Hr22 & H22)".
  iDestruct "H23" as (r23) "(%Hr23 & H23)".
  iDestruct "H24" as (r24) "(%Hr24 & H24)".
  iDestruct "H25" as (r25) "(%Hr25 & H25)".
  iDestruct "H26" as (r26) "(%Hr26 & H26)".
  iDestruct "H27" as (r27) "(%Hr27 & H27)".
  iAssert ("x8" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H8]" as "H8bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r8. iFrame. iPureIntro. exact Hr8. }
  iAssert ("x9" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H9]" as "H9bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r9. iFrame. iPureIntro. exact Hr9. }
  iAssert ("x18" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H18]" as "H18bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r18. iFrame. iPureIntro. exact Hr18. }
  iAssert ("x19" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H19]" as "H19bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r19. iFrame. iPureIntro. exact Hr19. }
  iAssert ("x20" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H20]" as "H20bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r20. iFrame. iPureIntro. exact Hr20. }
  iAssert ("x21" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H21]" as "H21bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r21. iFrame. iPureIntro. exact Hr21. }
  iAssert ("x22" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H22]" as "H22bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r22. iFrame. iPureIntro. exact Hr22. }
  iAssert ("x23" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H23]" as "H23bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r23. iFrame. iPureIntro. exact Hr23. }
  iAssert ("x24" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H24]" as "H24bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r24. iFrame. iPureIntro. exact Hr24. }
  iAssert ("x25" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H25]" as "H25bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r25. iFrame. iPureIntro. exact Hr25. }
  iAssert ("x26" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H26]" as "H26bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r26. iFrame. iPureIntro. exact Hr26. }
  iAssert ("x27" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H27]" as "H27bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r27. iFrame. iPureIntro. exact Hr27. }
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def)
    in "H8bits H9bits H18bits H19bits H20bits H21bits H22bits H23bits H24bits
      H25bits H26bits H27bits".
  iDestruct "H8bits" as (a8) "(H8 & %Ha8)".
  iDestruct "H9bits" as (a9) "(H9 & %Ha9)".
  iDestruct "H18bits" as (a18) "(H18 & %Ha18)".
  iDestruct "H19bits" as (a19) "(H19 & %Ha19)".
  iDestruct "H20bits" as (a20) "(H20 & %Ha20)".
  iDestruct "H21bits" as (a21) "(H21 & %Ha21)".
  iDestruct "H22bits" as (a22) "(H22 & %Ha22)".
  iDestruct "H23bits" as (a23) "(H23 & %Ha23)".
  iDestruct "H24bits" as (a24) "(H24 & %Ha24)".
  iDestruct "H25bits" as (a25) "(H25 & %Ha25)".
  iDestruct "H26bits" as (a26) "(H26 & %Ha26)".
  iDestruct "H27bits" as (a27) "(H27 & %Ha27)".
  have HspExtract : bv_extract 0 4 sp = BV 4 0.
  { apply bv_eq. rewrite bv_extract_0_unsigned. cbn. bv_solve. }
  have HretEq : Z_to_bv 64 (0x1594c + 4) = BV 64 0x15950 by bv_solve.
  iEval (rewrite HretEq) in "Hret".
  liARun.
  iExists (tail, items, tt)ₗ. cbn.
  iFrame "Hitems Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  iAssert (instr_pre 0x15950 (writeSuccessPost15950SetupSpec P))
    with "[Hnext]" as "HnextPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq. iExact "Hnext". }
  iApply (instr_pre_wand 0x15950 0x15950 true true with "HnextPre");
    [done | done |].
  iIntros "Hpost".
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(HpostSys & HpostCaller & HpostSaved & HpostRest)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "HpostCaller".
  iDestruct "HpostCaller" as
    "(Hpost1 & Hpost12 & Hpost13 & Hpost14 & Hpost15 & Hpost16 & Hpost17 &
      Hpost5 & Hpost6 & Hpost7 & Hpost28 & Hpost29 & Hpost30 & Hpost31 & _)".
  iDestruct "Hpost1" as (v1) "(%Hv1 & Hpost1)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "HpostRest".
  iDestruct "HpostRest" as (r10) "(Hpost10 & HpostRest)".
  iDestruct "HpostRest" as (b10') "(%Hr10 & HpostRest)". subst r10.
  iDestruct "HpostRest" as (r11) "(Hpost11 & HpostRest)".
  iDestruct "HpostRest" as (b11') "(%Hr11 & HpostRest)". subst r11.
  iDestruct "HpostRest" as "(Hpost2 & HpostStack & _)".
  iEval (rewrite /writeSuccessPost15950SetupSpec).
  iExists sp, pointer2, count2.
  iFrame "HpostSys Hpost2 Hstack56 Hstack48".
  iAssert ("x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[Hpost1]" as "Hpost1Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v1. iFrame. iPureIntro. exact Hv1. }
  iAssert ("x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[Hpost10]" as "Hpost10Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. iPureIntro. done. }
  iAssert ("x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[Hpost11]" as "Hpost11Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. iPureIntro. done. }
  iFrame "Hpost1Shape Hpost10Shape Hpost11Shape".
  repeat iSplit; try iPureIntro; try assumption; try lia; try bv_solve.
  iSplitL "Hcontinuation".
  - rewrite instr_pre'_eq.
    iExact "Hcontinuation".
  - iExact "HP".
  Unshelve. all: try prepare_sidecond.
  all: try bv_solve.
Qed.

Definition writeSuccessPost1595cCallEntrySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count value : bv 64)
      (b12 b13 b14 b15 b16 b17 : bv 64)
      (saved : list valu) (items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    reg_col (zip_with (fun r v => (KindReg r, BitsShape 64))
      writeSuccessPostByteListCallSaved saved) ∗
    ⌜length saved = 12%nat⌝ ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15958) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗ "x11" ↦ᵣ RVal_Bits count ∗
    "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗
    "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
    "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗
    (bv_unsigned sp - 80) ↦ₘ? 80 ∗
    (bv_unsigned sp + 56) ↦ₘ pointer ∗
    (bv_unsigned sp + 48) ↦ₘ count ∗
    (bv_unsigned sp + 64) ↦ₘ value ∗
    byteListItemResources (bv_unsigned pointer) items ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
        (byteListItemEvents (sp - BV 64 32)%bv items tail)) ∗
    ⌜bv_unsigned count = length items⌝ ∗
    ⌜length items < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (length items) < 0x40000000⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 80 /\
      bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 64 < 0x40000000⌝ ∗ P)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPost1595cCallEntrySpec) := I.

Lemma write_success_post_1595c_byte_lists_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  byteListsCode -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_pre 0x15968 (writeSuccessSuffixInt15968SetupSpec P) -∗
  instr_body 0x15960 (writeSuccessSuffixInt15960SetupSpec P) -∗
  instr_body 0x1595c (writeSuccessPost1595cCallEntrySpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode HbyteLists #Hint #Hbytes Hcontinuation Hnext".
  iPoseProof (write_success_byte_lists with "HbyteLists Hint Hbytes")
    as "HcalleeBody".
  iAssert (instr_pre 0x15c10 zesuEncoderByteListsCallSpec)%I
    with "[HcalleeBody]" as "Hcallee".
  { iApply instr_pre_to_body. iNext. iExact "HcalleeBody". }
  iPoseProof "Hlookup" as "#Hlookup1595c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1595c".
  iPoseProof ("Hlookup1595c" $! 0x1595c with "[]") as "#Hinstr1595c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1595c.
    done. }
  iPoseProof (IslaTraces.write_success_115.a1595c_spec.a1595c_spec
    0x1595c with "Hinstr1595c") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessPost1595cCallEntrySpec) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer count value b12 b13 b14 b15 b16 b17 saved items tail)
    "(Hsys & Htmp & Hsaved & %HsavedLength & H1 & H2 & H10 & H11 &
      H12 & H13 & H14 & H15 & H16 & H17 & Hstack80 & Hstack56 & Hstack48 &
      Hstack64 & Hitems & Hmmio & Htrace & %Hcount & %HitemsLength &
      %HfirstAlign & %HfirstLower & %HfirstUpper & %HspAlign & %HspBounds &
      %HspUpper64 & HP)".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x15958). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x15958) + BV 64 696)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15c10
    by bv_solve.
  rewrite Htarget.
  iEval (rewrite -instr_pre'_eq) in "Hcallee".
  iPoseProof (instr_pre_wand 0x15c10 0x15c10 true true
    with "Hcallee") as "Htarget"; [done | reflexivity |].
  iApply "Htarget".
  iIntros "(HsysCall & Hret & _ )".
  iEval (unfold zesuEncoderByteListsCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x15960).
  destruct saved as [|v8 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v9 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v18 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v19 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v20 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v21 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v22 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v23 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v24 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v25 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v26 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v27 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|vrest rest]; cbn in HsavedLength; try lia.
  iEval (unfold writeSuccessPostByteListCallSaved; cbn) in "Hsaved".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 &
      H26 & H27 & _)".
  iDestruct "H8" as (r8) "(%Hr8 & H8)".
  iDestruct "H9" as (r9) "(%Hr9 & H9)".
  iDestruct "H18" as (r18) "(%Hr18 & H18)".
  iDestruct "H19" as (r19) "(%Hr19 & H19)".
  iDestruct "H20" as (r20) "(%Hr20 & H20)".
  iDestruct "H21" as (r21) "(%Hr21 & H21)".
  iDestruct "H22" as (r22) "(%Hr22 & H22)".
  iDestruct "H23" as (r23) "(%Hr23 & H23)".
  iDestruct "H24" as (r24) "(%Hr24 & H24)".
  iDestruct "H25" as (r25) "(%Hr25 & H25)".
  iDestruct "H26" as (r26) "(%Hr26 & H26)".
  iDestruct "H27" as (r27) "(%Hr27 & H27)".
  iAssert ("x8" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H8]" as "H8bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r8. iFrame. iPureIntro. exact Hr8. }
  iAssert ("x9" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H9]" as "H9bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r9. iFrame. iPureIntro. exact Hr9. }
  iAssert ("x18" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H18]" as "H18bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r18. iFrame. iPureIntro. exact Hr18. }
  iAssert ("x19" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H19]" as "H19bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r19. iFrame. iPureIntro. exact Hr19. }
  iAssert ("x20" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H20]" as "H20bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r20. iFrame. iPureIntro. exact Hr20. }
  iAssert ("x21" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H21]" as "H21bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r21. iFrame. iPureIntro. exact Hr21. }
  iAssert ("x22" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H22]" as "H22bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r22. iFrame. iPureIntro. exact Hr22. }
  iAssert ("x23" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H23]" as "H23bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r23. iFrame. iPureIntro. exact Hr23. }
  iAssert ("x24" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H24]" as "H24bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r24. iFrame. iPureIntro. exact Hr24. }
  iAssert ("x25" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H25]" as "H25bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r25. iFrame. iPureIntro. exact Hr25. }
  iAssert ("x26" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H26]" as "H26bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r26. iFrame. iPureIntro. exact Hr26. }
  iAssert ("x27" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H27]" as "H27bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r27. iFrame. iPureIntro. exact Hr27. }
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def)
    in "H8bits H9bits H18bits H19bits H20bits H21bits H22bits H23bits H24bits
      H25bits H26bits H27bits".
  iDestruct "H8bits" as (a8) "(H8 & %Ha8)".
  iDestruct "H9bits" as (a9) "(H9 & %Ha9)".
  iDestruct "H18bits" as (a18) "(H18 & %Ha18)".
  iDestruct "H19bits" as (a19) "(H19 & %Ha19)".
  iDestruct "H20bits" as (a20) "(H20 & %Ha20)".
  iDestruct "H21bits" as (a21) "(H21 & %Ha21)".
  iDestruct "H22bits" as (a22) "(H22 & %Ha22)".
  iDestruct "H23bits" as (a23) "(H23 & %Ha23)".
  iDestruct "H24bits" as (a24) "(H24 & %Ha24)".
  iDestruct "H25bits" as (a25) "(H25 & %Ha25)".
  iDestruct "H26bits" as (a26) "(H26 & %Ha26)".
  iDestruct "H27bits" as (a27) "(H27 & %Ha27)".
  have HspExtract : bv_extract 0 4 sp = BV 4 0.
  { apply bv_eq. rewrite bv_extract_0_unsigned. cbn. bv_solve. }
  have HretEq : Z_to_bv 64 (0x1595c + 4) = BV 64 0x15960 by bv_solve.
  iEval (rewrite HretEq) in "Hret".
  liARun.
  iExists (tail, items, tt)ₗ. cbn.
  iFrame "Hitems Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  iAssert (instr_pre 0x15960 (writeSuccessSuffixInt15960SetupSpec P))
    with "[Hnext]" as "HnextPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq. iExact "Hnext". }
  iApply (instr_pre_wand 0x15960 0x15960 true true with "HnextPre");
    [done | done |].
  iIntros "Hpost".
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(HpostSys & HpostCaller & HpostSaved & HpostRest)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "HpostCaller".
  iDestruct "HpostCaller" as
    "(Hpost1 & Hpost12 & Hpost13 & Hpost14 & Hpost15 & Hpost16 & Hpost17 &
      Hpost5 & Hpost6 & Hpost7 & Hpost28 & Hpost29 & Hpost30 & Hpost31 & _)".
  iDestruct "Hpost1" as (v1) "(%Hv1 & Hpost1)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "HpostRest".
  iDestruct "HpostRest" as (r10) "(Hpost10 & HpostRest)".
  iDestruct "HpostRest" as (b10') "(%Hr10 & HpostRest)". subst r10.
  iDestruct "HpostRest" as (r11) "(Hpost11 & HpostRest)".
  iDestruct "HpostRest" as (b11') "(%Hr11 & HpostRest)". subst r11.
  iDestruct "HpostRest" as "(Hpost2 & HpostStack & _)".
  iEval (rewrite /writeSuccessSuffixInt15960SetupSpec).
  iExists sp, value.
  iFrame "HpostSys Hpost2 Hstack64".
  iAssert ("x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[Hpost1]" as "Hpost1Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v1. iFrame. iPureIntro. exact Hv1. }
  iAssert ("x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[Hpost10]" as "Hpost10Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. iPureIntro. done. }
  iFrame "Hpost1Shape Hpost10Shape".
  repeat iSplit; try iPureIntro; try assumption; try lia; try bv_solve.
  iSplitL "Hcontinuation".
  - rewrite instr_pre'_eq.
    iExact "Hcontinuation".
  - iExact "HP".
  Unshelve. all: try prepare_sidecond.
  all: try bv_solve.
Qed.
