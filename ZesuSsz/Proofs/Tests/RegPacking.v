Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.

Lemma four_argument_register_shapes `{!islaG Sigma} `{!threadG}
    (v10 v11 v12 v13 : bv 64) (P : iProp Sigma) :
  ("x10" ↦ᵣ RVal_Bits v10 ∗ "x11" ↦ᵣ RVal_Bits v11 ∗
   "x12" ↦ᵣ RVal_Bits v12 ∗ "x13" ↦ᵣ RVal_Bits v13 ∗ P ∗ True)%I -∗
  (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗ P ∗ True)%I.
Proof.
  iIntros "(H10 & H11 & H12 & H13 & HP & _)". iFrame "HP".
  iApply (reg_col_bv_list_shape [("x10", v10); ("x11", v11); ("x12", v12); ("x13", v13)]).
  cbn. iFrame.
Qed.
Print Assumptions four_argument_register_shapes.
