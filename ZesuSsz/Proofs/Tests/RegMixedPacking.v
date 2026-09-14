Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.

Lemma mixed_register_shapes `{!islaG Sigma} `{!threadG} (old5 old8 : bv 64) (P : iProp Sigma) :
  ("x5" ↦ᵣ RVal_Bits old5 ∗ "x8" ↦ᵣ RVal_Bits old8 ∗
   ("x6" ↦ᵣ: fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   reg_col [(KindReg "x7", BitsShape 64); (KindReg "x9", BitsShape 64)] ∗ P ∗ True)%I -∗
  (reg_col [(KindReg "x5", BitsShape 64); (KindReg "x6", BitsShape 64);
    (KindReg "x7", BitsShape 64); (KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64)] ∗ P ∗ True)%I.
Proof.
  iIntros "(H5 & H8 & H6 & Hremaining & HP & _)".
  iPoseProof (reg_col_shape_predicate with "H6") as "Hpredicate". iFrame "HP".
  iApply (reg_col_mixed_collect [("x5", old5); ("x8", old8)]
    [(KindReg "x6", BitsShape 64)] [(KindReg "x7", BitsShape 64); (KindReg "x9", BitsShape 64)]).
  - cbn. solve_Permutation.
  - cbn. iFrame.
Qed.
Print Assumptions mixed_register_shapes.
