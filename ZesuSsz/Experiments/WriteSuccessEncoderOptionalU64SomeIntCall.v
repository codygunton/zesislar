From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeBoundaries.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64SomePublicResume.

Lemma zesu_encoder_optional_u64_some_int_pre
    `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) :
  instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_pre 0x15d10
    (encoderOptionalSomeAtPublicInt data value sp ret tag tail P).
Proof.
  iStartProof. iIntros "Hint".
  iApply (instr_pre_wand 0x15d10 0x15d10 true true with "Hint");
    [done | done |].
  iIntros "Hentry".
  iEval (unfold encoderOptionalSomeAtPublicInt) in "Hentry".
  iDestruct "Hentry" as (old_x5 old_x8 old_x11)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H10 & H11 & Hstack & Hctx & _)".
  iEval (unfold encoderOptionalSomeContext) in "Hctx".
  iDestruct "Hctx" as
    "(Hdata & Htagmem & Hmmio & Htrace & %Htag & %Hdataalign &
      %Hdatamin & %Hdatamax & %Hspalign & %Hspalign8 & %Hspmin &
      %Hspmax & %Hret0 & %Hret1 & %Hret2 & HP & Hret & _)".
  iDestruct (mem_mapsto_uninit_split 16 with "Hstack") as
    "[Hlower Hupper]"; first lia.
  have HupperAddress : bv_unsigned sp - 32 + 16 = bv_unsigned sp - 16 by lia.
  iEval (rewrite HupperAddress; simpl) in "Hupper".
  iEval (unfold zesuEncoderIntCallSpec).
  iExists value, sp, (bv_unsigned ret), tail.
  rewrite Z_to_bv_bv_unsigned.
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys H1 H2 H5 H10 H11 Hupper Hmmio Htrace".
  repeat iSplit; try iPureIntro.
  all: try done.
  all: try (bv_simplify_arith Hspalign; bv_solve).
  all: try lia.
  all: try apply bv_unsigned_in_range.
  all: try (rewrite Z_to_bv_bv_unsigned; assumption).
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
      with "Hret"); [done | done |].
    iIntros "Hpost".
    iDestruct "Hpost" as
      "(Hsys & H1 & H2 & H5 & H10 & H11 & Hupper & Hmmio & Htrace & _)".
    iDestruct (mem_mapsto_uninit_split 8 with "Hlower") as
      "[Hstack0 Hstack1]"; first lia.
    iDestruct (mem_mapsto_uninit_split 8 with "Hupper") as
      "[Hstack2 Hstack3]"; first lia.
    have Hstack1Address : bv_unsigned sp - 32 + 8 = bv_unsigned sp - 24 by lia.
    have Hstack3Address : bv_unsigned sp - 16 + 8 = bv_unsigned sp - 8 by lia.
    iEval (rewrite Hstack1Address; simpl) in "Hstack1".
    iEval (rewrite Hstack3Address; simpl) in "Hstack3".
    iEval (unfold encoderOptionalSomeFinal).
    iExists (BV 64 0x15bfc).
    iFrame.
Qed.
