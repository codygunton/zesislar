Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec WriteSuccessExactWithdrawalsFields
  WriteSuccessExactWithdrawalsInt WriteSuccessExactWithdrawalsModel WriteSuccessExactEncoderIntFramedCall.

Lemma withdrawal_fields_to_tail `{!islaG Sigma} `{!threadG}
    sp pointer base rows prefix row rest source tail (P : iProp Sigma) :
  withdrawalFieldsPost sp row (writeSuccessExactWithdrawalEvents sp rest tail)
    (withdrawalBodyFrame sp pointer base rows prefix row rest source tail P) -∗
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   withdrawalTailPayload sp pointer base rows prefix row rest source tail P ∗ True)%I.
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hcopied & %Hrow & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H18 & Hbody & _)".
  iDestruct "Hbody" as "(H8 & H9 & Hothers & Hsource & HP & %Hfacts & Hexit & _)".
  iDestruct (byte_array_forget with "Hcopied") as "Hcopy".
  iEval (rewrite Hrow) in "Hcopy".
  iAssert (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
    ["x10"; "x11"; "x12"; "x13"; "x14"; "x15"]))%I with "[H10 H11 Hothers]" as "Hregs".
  { iApply (reg_col_mixed_collect [("x10", (sp - BV 64 16)%bv); ("x11", BV 64 8)] []
      [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
       (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)]).
    - solve_Permutation.
    - iFrame. rewrite big_sepL_nil reg_col_nil. done. }
  unfold withdrawalTailPayload. iFrame. done.
Qed.
Print Assumptions withdrawal_fields_to_tail.
