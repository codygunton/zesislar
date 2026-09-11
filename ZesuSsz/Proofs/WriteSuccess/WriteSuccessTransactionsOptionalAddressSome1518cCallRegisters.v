Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSomeHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1517cBoundary.

Lemma write_success_transactions_optional_address_some_1518c_call_registers
    `{!islaG Sigma} `{!threadG} :
  reg_col writeSuccessTransactions15168OtherRegShapes ∗
  "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
  "x12" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) -∗
  reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
  "x12" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
  "x13" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
  "x14" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
  "x15" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
  "x16" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
  "x17" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝).
Proof.
  iIntros "(Hother & H5 & H12)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as
    "(H3 & H4 & H6 & H7 & H13 & H14 & H15 & H16 & H17 & H28 & H29 & H30 &
      H31 & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iDestruct "H5" as (v5) "(H5 & %Hv5)".
  iDestruct "H13" as (v13) "(%Hv13 & H13)".
  iDestruct "H14" as (v14) "(%Hv14 & H14)".
  iDestruct "H15" as (v15) "(%Hv15 & H15)".
  iDestruct "H16" as (v16) "(%Hv16 & H16)".
  iDestruct "H17" as (v17) "(%Hv17 & H17)".
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers))%I
    with "[H5 H6 H7 H28 H29 H30 H31]" as "Htmp".
  { rewrite /tmp_registers !reg_col_cons reg_col_nil. iSplitL "H5".
    - iExists v5. iFrame "H5". iPureIntro. exact Hv5.
    - iFrame "H6 H7 H28 H29 H30 H31". }
  iAssert ("x13" ↦ᵣ: (fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H13]" as "H13P".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists v13.
    iFrame "H13". iPureIntro. exact Hv13. }
  iAssert ("x14" ↦ᵣ: (fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H14]" as "H14P".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists v14.
    iFrame "H14". iPureIntro. exact Hv14. }
  iAssert ("x15" ↦ᵣ: (fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H15]" as "H15P".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists v15.
    iFrame "H15". iPureIntro. exact Hv15. }
  iAssert ("x16" ↦ᵣ: (fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H16]" as "H16P".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists v16.
    iFrame "H16". iPureIntro. exact Hv16. }
  iAssert ("x17" ↦ᵣ: (fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H17]" as "H17P".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists v17.
    iFrame "H17". iPureIntro. exact Hv17. }
  rewrite !reg_col_cons reg_col_nil.
  iFrame "H3 H4 Htmp H12 H13P H14P H15P H16P H17P".
Qed.
