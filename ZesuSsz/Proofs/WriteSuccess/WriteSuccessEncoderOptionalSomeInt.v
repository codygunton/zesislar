Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeBoundaries.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Lemma encoder_optional_some_int `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10
    (encoderOptionalSomeAtInt data value sp ret tag tail P).
Proof.
  iStartProof. iIntros "#H07 #H01".
  iPoseProof (encoder_int_correct value sp ret tail P with "H07 H01")
    as "Hint".
  rewrite instr_pre'_eq.
  iIntros "Hentry".
  iEval (unfold encoderOptionalSomeAtInt) in "Hentry".
  iDestruct "Hentry" as (old_x8)
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
  iDestruct (mem_mapsto_uninit_split 8 with "Hupper") as
    "[Hstack0 Hstack8]"; first lia.
  have Hstack8Address : bv_unsigned sp - 16 + 8 = bv_unsigned sp - 8 by lia.
  iEval (rewrite Hstack8Address; simpl) in "Hstack8".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hstack0") as
    (n0 stack0 Hn0) "Hstack0".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hstack8") as
    (n8 stack8 Hn8) "Hstack8".
  cbn in Hn0, Hn8. subst n0 n8.
  iApply "Hint".
  iExists (BV 64 0x2401a0b8), (BV 64 1), stack0, stack8.
  iFrame "Hsys H1 H2 H5 H10 H11 Hstack0 Hstack8 Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  iSplitL "HP"; first iFrame.
  iSplit; last done.
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hret"); [done | done |].
  iIntros "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack0 & Hstack8 &
      Hmmio & Htrace & HP & _)".
  iDestruct (mem_mapsto_uninit_split 8 with "Hlower") as
    "[Hstack32 Hstack24]"; first lia.
  have Hstack24Address : bv_unsigned sp - 32 + 8 = bv_unsigned sp - 24 by lia.
  iEval (rewrite Hstack24Address; simpl) in "Hstack24".
  iPoseProof (mem_mapsto_mapsto_to_uninit with "Hstack0") as "Hstack16".
  iPoseProof (mem_mapsto_mapsto_to_uninit with "Hstack8") as "Hstack8".
  iEval (unfold encoderOptionalSomeFinal).
  iExists (BV 64 0x15bfc).
  iFrame.
Qed.
