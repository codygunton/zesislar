Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

Lemma zesu_c_call_ret_16_to_32 `{!islaG Sigma} `{!threadG}
    (regs : list valu) (ret sp : bv 64) (Q : list (bv 64) -> iProp Sigma) :
  instr_pre (bv_unsigned ret) (zesu_c_call_ret 32 regs ret sp Q) -∗
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret 16 regs ret sp (fun args =>
      (bv_unsigned sp - 32) ↦ₘ? 16 ∗ Q args)).
Proof.
  iStartProof. iIntros "Hret".
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hret"); [done | done |].
  iEval (unfold zesu_c_call_ret).
  iIntros "(Hsys & Htmp & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11 & H2 & Hupper & Hlower & HQ)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp Hsaved H10 H11 H2".
  iExists b10. iSplit; first done.
  iExists b11. iSplit; first done.
  iFrame "HQ".
  iApply (mem_mapsto_uninit_combine 16 with "Hlower"); first lia.
  have -> : bv_unsigned sp - 32 + 16 = bv_unsigned sp - 16 by lia.
  iExact "Hupper".
Qed.

Lemma zesu_c_call_ret_frame `{!islaG Sigma} `{!threadG}
    (stack_size : Z) (regs : list valu) (ret sp : bv 64)
    (F : iProp Sigma) (Q : list (bv 64) -> iProp Sigma) :
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stack_size regs ret sp (fun args => F ∗ Q args)) -∗
  F -∗
  instr_pre (bv_unsigned ret) (zesu_c_call_ret stack_size regs ret sp Q).
Proof.
  iStartProof. iIntros "Hret HF".
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hret"); [done | done |].
  iEval (unfold zesu_c_call_ret).
  iIntros "(Hsys & Htmp & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11 & H2 & Hstack & HQ)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp Hsaved H10 H11 H2 Hstack".
  iExists b10. iSplit; first done.
  iExists b11. iSplit; first done.
  iFrame.
Qed.
