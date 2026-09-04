From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBoolean.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalNoneBoundaries.

Lemma encoder_optional_none_boolean `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c (encoderOptionalNoneAtBoolean data value sp ret tail P).
Proof.
  iStartProof. iIntros "#H03 #H01".
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as
    (old_x5 old_x6 old_x8 stackByte stackRa)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H10 & H11 &
      Hvalue & Htag & Hstack & HstackByte & HstackRa & Hmmio & Htrace &
      %Hdataalign & %Hdatamin & %Hdatamax & %Hspalign4 & %Hspalign3 &
      %Hspmin & %Hspmax & %Hret0 & %Hret1 & %Hret2 & HP & Hret & _)".
  iPoseProof (encoder_boolean_correct (BV 64 0) sp ret tail
    ("x8" ↦ᵣ RVal_Bits old_x8 ∗
     bv_unsigned data ↦ₘ value ∗
     (bv_unsigned data + 8) ↦ₘ (BV 8 0) ∗ P)%I
    with "H03 H01") as "Hbody".
  rewrite instr_pre'_eq. iApply "Hbody".
  iExists old_x5, (BV 64 0), stackByte, stackRa.
  iFrame "Hsys H1 H2 H5 H10 H11 Hstack HstackByte HstackRa Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  iAssert (instr_pre (bv_unsigned ret)
    (reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
     "x10" ↦ᵣ RVal_Bits ((sp - BV 64 9)%bv) ∗
     "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
     (bv_unsigned sp - 16) ↦ₘ? 7 ∗
     (bv_unsigned sp - 9) ↦ₘ
       (bv_extract 0 8 (bv_and (BV 64 0) (BV 64 1))) ∗
     (bv_unsigned sp - 8) ↦ₘ ret ∗
     mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗
     ("x8" ↦ᵣ RVal_Bits old_x8 ∗
      bv_unsigned data ↦ₘ value ∗
      (bv_unsigned data + 8) ↦ₘ (BV 8 0) ∗ P) ∗ True))%I
    with "[Hret H6]" as "HbooleanRet".
  { iEval (rewrite <- instr_pre'_eq) in "Hret".
    iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
      with "Hret").
    - done.
    - done.
    -
    iIntros "Hpost".
    iDestruct "Hpost" as
      "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & HstackByte & HstackRa &
        Hmmio & Htrace & HP & _)".
    have Hzero : bv_extract 0 8 (bv_and (BV 64 0) (BV 64 1)) = BV 8 0 by
      bv_solve.
    rewrite Hzero.
    rewrite /encoderOptionalNoneFinal.
    iExists old_x6.
    iDestruct "HP" as "(H8 & Hvalue & Htag & HP)".
    iEval (simpl).
    iEval (simpl) in "HstackByte".
    iFrame "Hsys H1 H2 H5 H6 H8 H10 H11 Hvalue Htag Hstack HstackByte
      HstackRa Hmmio Htrace HP". }
  iFrame "H8 Hvalue Htag HP HbooleanRet".
Qed.
