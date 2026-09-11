Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.

Lemma write_success_transactions_10190_caller_adapter
    `{!islaG Sigma} `{!threadG} (b10 b11 : bv 64) :
  reg_col
    [(KindReg "x1", BitsShape 64); (KindReg "x12", BitsShape 64);
     (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64);
     (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64);
     (KindReg "x17", BitsShape 64); (KindReg "x5", BitsShape 64);
     (KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
     (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
     (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)] -∗
  "x10" ↦ᵣ RVal_Bits b10 -∗
  "x11" ↦ᵣ RVal_Bits b11 -∗
  reg_col writeSuccessTransactions150e8OtherRegShapes -∗
  reg_col writeSuccessTransactions150f0OtherRegShapes.
Proof.
  iIntros "Hcaller H10 H11 Hother".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hcaller Hother".
  iDestruct "Hcaller" as
    "(H1 & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 &
      H29 & H30 & H31 & _)".
  iDestruct "Hother" as "(H3 & H4 & _)".
  rewrite /writeSuccessTransactions150f0OtherRegShapes
    /writeSuccessTransactions150f0OtherRegisters /= !reg_col_cons reg_col_nil.
  iFrame.
  repeat iSplit; try iPureIntro; try (cbn; done).
Qed.
