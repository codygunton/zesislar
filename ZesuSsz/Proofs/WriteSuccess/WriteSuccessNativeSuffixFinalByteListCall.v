From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_125 Require Import a159d4_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEpilogueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixFinalCallSetup.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixByteListCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.

Import ListNotations.

Definition writeSuccessFinalSavedRegisters : list string :=
  ["x9"; "x18"; "x19"; "x20"; "x21"; "x22";
   "x23"; "x24"; "x25"; "x26"; "x27"].

Definition writeSuccessFinalCallArgRegisters : list string :=
  ["x13"; "x14"; "x15"; "x16"; "x17"].

Definition writeSuccessFinalOtherRegisters : list string := ["x3"; "x4"].

Definition writeSuccessFinalCallEntryFrame
    `{!islaG Sigma} `{!threadG}
    (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec)
  (P : iProp Sigma) : iProp Sigma :=
  (∃ (b12 b13 b14 b15 b16 b17 : bv 64)
      (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64),
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessFinalOtherRegisters) ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessFinalSavedRegisters) ∗
    "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗
    "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
    "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗
    (bv_unsigned sp - 80) ↦ₘ? 80 ∗
    byteListItemResources (bv_unsigned pointer) items ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (byteListItemEvents (sp - BV 64 32)%bv items tail)) ∗
    ⌜bv_unsigned count = length items⌝ ∗
    ⌜length items < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (length items) < 0x40000000⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 80⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    (writeSuccessEpilogueSavedSlots sp (BV 64 0x159d8)
      s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 1896⌝ ∗
    ⌜bv_unsigned sp + 2000 < 0x40000000⌝ ∗
    ⌜bv_extract 0 1 (BV 64 0x159d8) = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 (BV 64 0x159d8) = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 (BV 64 0x159d8) = BV 2 0⌝ ∗
    P ∗
    instr_pre 0x159d8
      (writeSuccessEpiloguePost sp (BV 64 0x159d8)
        s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P))%I.

Global Instance : LithiumUnfold (@writeSuccessFinalCallEntryFrame) := I.

Definition writeSuccessPost159d4CallEntrySpec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x159d0) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗
    "x11" ↦ᵣ RVal_Bits count ∗
    writeSuccessFinalCallEntryFrame sp pointer count items tail Q)%I.

Global Instance : LithiumUnfold (@writeSuccessPost159d4CallEntrySpec) := I.

Lemma write_success_final_saved_col
    `{!islaG Sigma} `{!threadG} (pointer : bv 64) :
  "x8" ↦ᵣ RVal_Bits pointer ∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    writeSuccessFinalSavedRegisters) -∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
     "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]).
Proof.
  iIntros "(H8 & Hsaved)".
  iEval (rewrite /writeSuccessFinalSavedRegisters; cbn) in "Hsaved".
  cbn. iFrame "Hsaved".
  iExists (RVal_Bits pointer). iFrame. done.
Qed.

Lemma write_success_post_159d4_byte_lists_call
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  byteListsCode -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x159d8 (writeSuccessEpilogueSpec Q) -∗
  instr_body 0x159d4 (writeSuccessPost159d4CallEntrySpec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode HbyteLists #Hint #Hbytes Hnext".
  iPoseProof (write_success_byte_lists with "HbyteLists Hint Hbytes")
    as "HcalleeBody".
  iAssert (instr_pre 0x15c10 zesuEncoderByteListsCallSpec)%I
    with "[HcalleeBody]" as "Hcallee".
  { iApply instr_pre_to_body. iNext. iExact "HcalleeBody". }
  iPoseProof "Hlookup" as "#Hlookup159d4".
  iEval (rewrite /instr_lookup_resources) in "Hlookup159d4".
  iPoseProof ("Hlookup159d4" $! 0x159d4 with "[]") as "#Hinstr159d4".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a159d4.
    done. }
  iPoseProof (IslaTraces.write_success_125.a159d4_spec.a159d4_spec
    0x159d4 with "Hinstr159d4") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessPost159d4CallEntrySpec) in "Hentry".
  iDestruct "Hentry" as (sp pointer count items tail)
    "(Hsys & H1 & H2 & H8 & H10 & H11 & Hframe)".
  iEval (rewrite /writeSuccessFinalCallEntryFrame) in "Hframe".
  iDestruct "Hframe" as
    (b12 b13 b14 b15 b16 b17
      s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    "(Htmp & Hother & Hsaved & H12 & H13 & H14 &
      H15 & H16 & H17 & Hstack80 & Hitems & Hmmio & Htrace & %Hcount &
      %HitemsLength & %HfirstAlign & %HfirstLower & %HfirstUpper &
      %HspExtract & %HspLower & %HspUpper & Hslots & %HspAlign &
      %Hsp1896 & %Hsp2000 & %Hret1 & %Hret2 & %Hret & HQ & Hreturn)".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x159d0). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x159d0) + BV 64 576)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15c10
    by bv_solve.
  rewrite Htarget.
  iEval (rewrite -instr_pre'_eq) in "Hcallee".
  iPoseProof (instr_pre_wand 0x15c10 0x15c10 true true
    with "Hcallee") as "Htarget"; [done | reflexivity |].
  iApply "Htarget".
  iIntros "(HsysCall & Hret & _)".
  iEval (unfold zesuEncoderByteListsCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x159d8).
  iPoseProof (write_success_final_saved_col pointer
    with "[$H8 $Hsaved]") as "HsavedFull".
  have HretEq : Z_to_bv 64 (0x159d4 + 4) = BV 64 0x159d8 by bv_solve.
  iEval (rewrite HretEq) in "Hret".
  liARun.
  iExists (tail, items, tt)ₗ. cbn.
  iFrame "Hitems Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try lia; try bv_solve.
  iAssert (instr_pre 0x159d8 (writeSuccessEpilogueSpec Q))
    with "[Hnext]" as "HnextPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq. iExact "Hnext". }
  iApply (instr_pre_wand 0x159d8 0x159d8 true true with "HnextPre");
    [done | done |].
  iIntros "Hpost".
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(HpostSys & HpostCaller & HpostSaved & HpostRest)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "HpostCaller".
  iDestruct "HpostCaller" as
    "(Hpost1 & Hpost12 & Hpost13 & Hpost14 & Hpost15 & Hpost16 & Hpost17 &
      Hpost5 & Hpost6 & Hpost7 & Hpost28 & Hpost29 & Hpost30 & Hpost31 & _)".
  iDestruct "Hpost1" as (post1) "(%Hpost1Shape & Hpost1)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "HpostRest".
  iDestruct "HpostRest" as (r10) "(Hpost10 & HpostRest)".
  iDestruct "HpostRest" as (post10) "(%Hr10 & HpostRest)".
  iDestruct "HpostRest" as (r11) "(Hpost11 & HpostRest)".
  iDestruct "HpostRest" as (post11)
    "(%Hr11 & Hpost2 & HpostStack & HpostItems & HpostMmio & HpostTrace & _)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "HpostSaved".
  iDestruct "HpostSaved" as
    "(Hpost8 & Hpost9 & Hpost18 & Hpost19 & Hpost20 & Hpost21 & Hpost22 &
      Hpost23 & Hpost24 & Hpost25 & Hpost26 & Hpost27 & _)".
  iDestruct "Hpost8" as (post8) "(_ & Hpost8)".
  iDestruct "Hpost9" as (post9) "(_ & Hpost9)".
  iDestruct "Hpost18" as (post18) "(_ & Hpost18)".
  iDestruct "Hpost19" as (post19) "(_ & Hpost19)".
  iDestruct "Hpost20" as (post20) "(_ & Hpost20)".
  iDestruct "Hpost21" as (post21) "(_ & Hpost21)".
  iDestruct "Hpost22" as (post22) "(_ & Hpost22)".
  iDestruct "Hpost23" as (post23) "(_ & Hpost23)".
  iDestruct "Hpost24" as (post24) "(_ & Hpost24)".
  iDestruct "Hpost25" as (post25) "(_ & Hpost25)".
  iDestruct "Hpost26" as (post26) "(_ & Hpost26)".
  iDestruct "Hpost27" as (post27) "(_ & Hpost27)".
  iEval (rewrite /writeSuccessEpilogueSpec).
  iExists sp, (BV 64 0x159d8), s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11.
  iSplitL "HpostSys"; first iExact "HpostSys".
  iEval (rewrite /WriteSuccessPrologueSpec.writeSuccessOtherRegShapes
    /WriteSuccessPrologueSpec.writeSuccessOtherRegisters
    !reg_col_cons reg_col_nil).
  iDestruct "Hother" as "(Hpost3 & Hpost4 & _)".
  iFrame "Hpost3 Hpost4 Hpost5 Hpost6 Hpost7 Hpost13 Hpost14 Hpost15 Hpost16
    Hpost17 Hpost28 Hpost29 Hpost30 Hpost31".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iExists post1.
  iFrame "Hpost1 Hpost2".
  iExists post8. iFrame "Hpost8".
  iExists post9. iFrame "Hpost9".
  iExists post18. iFrame "Hpost18".
  iExists post19. iFrame "Hpost19".
  iExists post20. iFrame "Hpost20".
  iExists post21. iFrame "Hpost21".
  iExists post22. iFrame "Hpost22".
  iExists post23. iFrame "Hpost23".
  iExists post24. iFrame "Hpost24".
  iExists post25. iFrame "Hpost25".
  iExists post26. iFrame "Hpost26".
  iExists post27. iFrame "Hpost27 Hslots HQ".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve;
    try iFrame "Hreturn"; try done.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try match goal with
    | |- bv_unsigned ?stack `mod` 16 = 0 =>
        bv_simplify_arith HspExtract; bv_solve
    end.
  all: lazymatch goal with |- ?G => fail "suffix final residual" G end.
Qed.
