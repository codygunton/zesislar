From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBoolean.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeBoundaries.

Lemma encoder_optional_some_boolean_call `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bec
    (encoderOptionalSomeAtResume data value sp ret tag tail P) -∗
  instr_body 0x15b9c
    (encoderOptionalSomeAtBoolean data value sp ret tag tail P).
Proof.
  iStartProof. iIntros "#H03 #H01 Hnext".
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as (old_x5 old_x6 old_x8)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H10 & H11 & Hstack &
      Hstack8 & HstackRet & Hctx & _)".
  iEval (unfold encoderOptionalSomeContext) in "Hctx".
  iDestruct "Hctx" as
    "(Hdata & Htagmem & Hmmio & Htrace & %Htag & %Hdataalign &
      %Hdatamin & %Hdatamax & %Hspalign & %Hspalign8 & %Hspmin &
      %Hspmax & %Hret0 & %Hret1 & %Hret2 & HP & Hret & _)".
  iDestruct (mem_mapsto_uninit_split 7 with "Hstack") as
    "[Hstack7 HstackRest]"; first lia.
  iDestruct (mem_mapsto_uninit_split 1 with "HstackRest") as
    "[HstackByte HstackRa]"; first lia.
  have HstackByteAddress : bv_unsigned sp - 32 + 7 = bv_unsigned sp - 25 by lia.
  iEval (rewrite HstackByteAddress; simpl) in "HstackByte".
  have HstackRaAddress : bv_unsigned sp - 32 + 7 + 1 = bv_unsigned sp - 24 by lia.
  iEval (rewrite HstackRaAddress; simpl) in "HstackRa".
  iDestruct (mem_mapsto_uninit_to_mapsto with "HstackByte") as
    (nByte stackByte HnByte) "HstackByte".
  iDestruct (mem_mapsto_uninit_to_mapsto with "HstackRa") as
    (nRa stackRa HnRa) "HstackRa".
  cbn in HnByte, HnRa. subst nByte nRa.
  iPoseProof (encoder_boolean_correct (BV 64 1) (sp - BV 64 16)
    (BV 64 0x15bec) (encoderOptionalSomeAfterBooleanEvents sp tail)
    ("x6" ↦ᵣ RVal_Bits old_x6 ∗ "x8" ↦ᵣ RVal_Bits value ∗
     bv_unsigned data ↦ₘ value ∗ (bv_unsigned data + 8) ↦ₘ tag ∗
     (bv_unsigned sp - 16) ↦ₘ old_x8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
     P ∗ instr_pre (bv_unsigned ret)
       (encoderOptionalSomeFinal data value sp ret tag old_x8 tail P))%I
    with "H03 H01") as "Hbody".
  rewrite instr_pre'_eq. iApply "Hbody".
  iExists old_x5, (bv_zero_extend 64 tag),
    (bv_zero_extend 64 stackByte), stackRa.
  have HspSubUnsigned : bv_unsigned (sp - BV 64 16) = bv_unsigned sp - 16 by
    bv_simplify_arith Hspalign; bv_solve.
  have HcalleeStack : bv_unsigned (sp - BV 64 16) - 16 = bv_unsigned sp - 32 by
    rewrite HspSubUnsigned; lia.
  have HcalleeByte : bv_unsigned (sp - BV 64 16) - 9 = bv_unsigned sp - 25 by
    rewrite HspSubUnsigned; lia.
  have HcalleeRa : bv_unsigned (sp - BV 64 16) - 8 = bv_unsigned sp - 24 by
    rewrite HspSubUnsigned; lia.
  have HbyteExtend : bv_extract 0 8 (bv_zero_extend 64 stackByte) = stackByte by
    bv_simplify; done.
  have HbooleanEvent : (sp - BV 64 16 - BV 64 9)%bv =
    (sp - BV 64 16 - BV 64 16 + BV 64 7)%bv by bv_solve.
  iEval (unfold encoderOptionalSomeInitialEvents) in "Htrace".
  iEval (rewrite <- HbooleanEvent) in "Htrace".
  iEval (rewrite HcalleeStack HcalleeByte HcalleeRa HbyteExtend).
  iFrame "Hsys H1 H2 H5 H10 H11 Hstack7 HstackByte HstackRa Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  all: try (bv_simplify_arith Hspalign; bv_solve).
  all: try (rewrite HcalleeStack; lia).
  iSplitL "H6 H8 Hdata Htagmem Hstack8 HstackRet HP Hret".
  { iFrame. }
  iSplit; last done.
  iAssert (instr_pre 0x15bec
    (encoderOptionalSomeAtResume data value sp ret tag tail P))%I
    with "[Hnext]" as "Hresume".
  { iApply instr_pre_to_body. iNext.
    iEval (rewrite instr_pre'_eq). iExact "Hnext". }
  iApply (instr_pre_wand 0x15bec 0x15bec true true with "Hresume");
    [done | done |].
  iIntros "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack7 & HstackByte &
      HstackRa & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as
    "(H6 & H8 & Hdata & Htagmem & Hstack8 & HstackRet & HP & Hret)".
  have Hone : bv_extract 0 8 (bv_and (BV 64 1) (BV 64 1)) = BV 8 1 by
    bv_solve.
  rewrite Hone.
  iEval (unfold encoderOptionalSomeAtResume, encoderOptionalSomeContext).
  iExists old_x6, old_x8.
  iFrame.
  have HresumeArg : (sp - BV 64 16 - BV 64 9)%bv =
    (sp - BV 64 25)%bv by bv_solve.
  iEval (rewrite HresumeArg) in "H10".
  iEval (rewrite instr_pre'_eq).
  iFrame "H10 Hret".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
Qed.
