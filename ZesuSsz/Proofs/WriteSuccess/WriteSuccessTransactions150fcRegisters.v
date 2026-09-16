Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15104.

Lemma write_success_transactions_150fc_registers `{!islaG Sigma} `{!threadG} :
  reg_col
    [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64);
     (KindReg "x5", BitsShape 64); (KindReg "x6", BitsShape 64);
     (KindReg "x7", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64);
     (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64);
     (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
     (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)] -∗
  reg_col writeSuccessTransactions15104OtherRegShapes ∗
  ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
  ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝).
Proof.
  iIntros "Hregs".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hregs".
  iDestruct "Hregs" as
    "(H3 & H4 & H5 & H6 & H7 & H11 & H12 & H13 & H14 & H15 &
      H16 & H17 & H28 & H29 & H30 & H31 & _)".
  iDestruct "H5" as (v5 Hshape5) "H5".
  iDestruct "H11" as (v11 Hshape11) "H11".
  iAssert ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝)%I
    with "[H5]" as "H5target".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v5. iFrame. iPureIntro. exact Hshape5. }
  iAssert ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝)%I
    with "[H11]" as "H11target".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v11. iFrame. iPureIntro. exact Hshape11. }
  iAssert (reg_col writeSuccessTransactions15104OtherRegShapes)
    with "[H3 H4 H6 H7 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31]"
    as "HtargetRegs".
  { rewrite !reg_col_cons reg_col_nil. iFrame. }
  iFrame.
Qed.
