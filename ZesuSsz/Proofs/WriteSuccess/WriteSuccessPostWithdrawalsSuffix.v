Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixRoot.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostWithdrawalsBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostWithdrawalsOptional.

Definition writeSuccessPostWithdrawalsSuffixFrame
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size : bv 64)
    (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 48 ∗
   bv_unsigned (sp + BV 64 1624)%bv ↦ₘ optionalValue ∗
   (bv_unsigned (sp + BV 64 1624)%bv + 8) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
   (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1168) ↦ₘ data ∗
   (bv_unsigned sp + 1176) ↦ₘ size ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsSuffixFrame) := I.

Lemma write_success_post_withdrawals_suffix_adapter
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) :
  writeSuccessPostWithdrawalsAt1572cState sp optionalValue optionalTag data
    size root bytes saved tail P ⊢
  writeSuccessSuffixAt1572c
    (writeSuccessPostWithdrawalsSuffixFrame sp optionalValue optionalTag
      data size bytes P).
Proof.
  iIntros "Hentry".
  iEval (unfold writeSuccessPostWithdrawalsAt1572cState) in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H5 & H6 & H10 & H11 & Hother & Hsaved &
      %HsavedLength & Hstack & HoptionalValue & HoptionalTag & HslotValue &
      HslotTag & HslotData & HslotSize & Hroot & Hdata & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & %Hupper & HP & _)".
  iPoseProof (post_withdrawals_saved_bits saved with "[] Hsaved")
    as "HsavedBits".
  { iPureIntro. exact HsavedLength. }
  rewrite /writeSuccessSuffixAt1572c.
  iExists sp, root, data, size, tail.
  iFrame "Hsys H1 H2 H5 H10 H11 Hmmio Htrace Hroot".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  rewrite /writeSuccessSuffixRootFrame
    /writeSuccessPostWithdrawalsSuffixFrame
    /writeSuccessSuffixRootOtherRegisters
    /writeSuccessPostWithdrawalsCallRegisters.
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iEval (rewrite !reg_col_cons reg_col_nil).
  iDestruct "Hother" as
    "(H3 & H4 & H7 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29 &
      H30 & H31 & _)".
  iDestruct "HsavedBits" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
      H27 & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in
    "H6 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27".
  iDestruct "H6" as (v6) "(H6 & %Hv6)".
  iDestruct "H8" as (v8) "(H8 & %Hv8)".
  iDestruct "H9" as (v9) "(H9 & %Hv9)".
  iDestruct "H18" as (v18) "(H18 & %Hv18)".
  iDestruct "H19" as (v19) "(H19 & %Hv19)".
  iDestruct "H20" as (v20) "(H20 & %Hv20)".
  iDestruct "H21" as (v21) "(H21 & %Hv21)".
  iDestruct "H22" as (v22) "(H22 & %Hv22)".
  iDestruct "H23" as (v23) "(H23 & %Hv23)".
  iDestruct "H24" as (v24) "(H24 & %Hv24)".
  iDestruct "H25" as (v25) "(H25 & %Hv25)".
  iDestruct "H26" as (v26) "(H26 & %Hv26)".
  iDestruct "H27" as (v27) "(H27 & %Hv27)".
  iFrame.
  all: iPureIntro; try assumption; try done.
Qed.

Print Assumptions write_success_post_withdrawals_suffix_adapter.
