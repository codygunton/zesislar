Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.

Lemma write_success_call_ret_frame_right
    `{!islaG Sigma} `{!threadG}
    (stackSize : Z) (regs : list valu) (ret sp : bv 64)
    (Q : list (bv 64) -> iProp Sigma) (F : iProp Sigma) :
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stackSize regs ret sp (fun args => Q args ∗ F ∗ True)) -∗
  F -∗
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stackSize regs ret sp (fun args => Q args ∗ True)).
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
  iDestruct "Hrest" as (b11) "(%Hr11 & H2 & Hstack & HQ & HF')".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp Hsaved H10 H11 H2 Hstack HQ HF".
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.

Lemma write_success_call_ret_frame_right2
    `{!islaG Sigma} `{!threadG}
    (stackSize : Z) (regs : list valu) (ret sp : bv 64)
    (Q1 Q2 : list (bv 64) -> iProp Sigma) (F : iProp Sigma) :
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stackSize regs ret sp
      (fun args => Q1 args ∗ Q2 args ∗ F ∗ True)) -∗
  F -∗
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stackSize regs ret sp
      (fun args => Q1 args ∗ Q2 args ∗ True)).
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
  iDestruct "Hrest" as (b11) "(%Hr11 & H2 & Hstack & HQ1 & HQ2 & HF')".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp Hsaved H10 H11 H2 Hstack HQ1 HQ2 HF".
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
