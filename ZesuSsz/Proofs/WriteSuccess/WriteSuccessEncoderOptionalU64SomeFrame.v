Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeBoundaries.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64SomeFrameDefinitions.

Lemma optional_u64_some_public_return
    `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8) (tail : spec)
    (r8 r9 r12 r13 r14 r15 r16 r17
     r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : bv 64) :
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret 32
      [RVal_Bits r8; RVal_Bits r9; RVal_Bits r18; RVal_Bits r19;
       RVal_Bits r20; RVal_Bits r21; RVal_Bits r22; RVal_Bits r23;
       RVal_Bits r24; RVal_Bits r25; RVal_Bits r26; RVal_Bits r27]
      ret sp
      (fun _ =>
        bv_unsigned data ↦ₘ value ∗ (bv_unsigned data + 8) ↦ₘ tag ∗
        mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)) -∗
  instr_pre (bv_unsigned ret)
    (encoderOptionalSomeFinal data value sp ret tag r8 tail
      (optionalU64SomePublicFrame r9 r12 r13 r14 r15 r16 r17
        r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)).
Proof.
  iStartProof. iIntros "Hret".
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hret"); [done | done |].
  iIntros "Hfinal".
  iEval (unfold encoderOptionalSomeFinal) in "Hfinal".
  iDestruct "Hfinal" as (final_x6)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H10 & H11 & Hdata & Htag &
      Hstack0 & Hstack1 & Hstack2 & Hstack3 & Hmmio & Htrace & HP & _)".
  iEval (unfold optionalU64SomePublicFrame) in "HP".
  iDestruct "HP" as "(Htmp & Hcaller & Hsaved)".
  iEval (rewrite !reg_col_cons reg_col_nil) in
    "Htmp Hcaller Hsaved".
  iDestruct "Htmp" as "(H7 & H28 & H29 & H30 & H31 & _)".
  iDestruct "Hcaller" as "(H12 & H13 & H14 & H15 & H16 & H17 & _)".
  iDestruct "Hsaved" as
    "(H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
  iEval (unfold zesu_c_call_ret).
  rewrite !reg_col_cons reg_col_nil.
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys H1 H2 H5 H6 H8 H10 H11 H7 H28 H29 H30 H31
    H12 H13 H14 H15 H16 H17 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27".
  repeat iSplit; try iPureIntro; try done.
  iExists (sp - BV 64 16)%bv. iSplit; first done.
  iExists (BV 64 8). iSplit; first done.
  iSplitL "Hstack0 Hstack1 Hstack2 Hstack3".
  - iApply (@mem_mapsto_uninit_combine _ _ 8 _ _ 32 with "Hstack0");
      first lia.
    have Hstack1Address : bv_unsigned sp - 32 + 8 = bv_unsigned sp - 24 by lia.
    rewrite Hstack1Address.
    iApply (@mem_mapsto_uninit_combine _ _ 8 _ _ 24 with "Hstack1");
      first lia.
    have Hstack2Address : bv_unsigned sp - 24 + 8 = bv_unsigned sp - 16 by lia.
    rewrite Hstack2Address.
    iApply (@mem_mapsto_uninit_combine _ _ 8 _ _ 16 with "Hstack2");
      first lia.
    have Hstack3Address : bv_unsigned sp - 16 + 8 = bv_unsigned sp - 8 by lia.
    rewrite Hstack3Address.
    iExact "Hstack3".
  - iFrame.
Qed.
