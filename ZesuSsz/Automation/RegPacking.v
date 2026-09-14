Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.

Lemma reg_col_bv_list_shape `{!islaG Sigma} `{!threadG}
    (registers : list (string * bv 64)) :
  ([∗ list] entry ∈ registers, entry.1 ↦ᵣ RVal_Bits (entry.2 : bv 64))%I -∗
  reg_col ((fun entry => (KindReg entry.1, BitsShape 64)) <$> registers).
Proof.
  induction registers as [|[register value] registers IH].
  - rewrite reg_col_nil. auto.
  - rewrite big_sepL_cons /= reg_col_cons. iIntros "[Hhead Htail]".
    iSplitL "Hhead"; first (iExists (RVal_Bits value); iFrame; done).
    iApply IH. iExact "Htail".
Qed.
Print Assumptions reg_col_bv_list_shape.

Lemma reg_col_shape_predicate `{!islaG Sigma} `{!threadG} register shape :
  (register ↦ᵣ: fun value => ⌜valu_has_shape value shape⌝)%I -∗
  reg_col [(KindReg register, shape)].
Proof.
  rewrite reg_mapsto_pred_eq reg_col_cons reg_col_nil.
  iIntros "(%value & Hregister & %Hshape)". iSplit; last done. iExists value. iFrame. done.
Qed.

Lemma reg_col_mixed_collect `{!islaG Sigma} `{!threadG}
    (values : list (string * bv 64)) predicates remaining requested :
  requested ≡ₚ ((fun entry => (KindReg entry.1, BitsShape 64)) <$> values) ++ predicates ++ remaining ->
  (([∗ list] entry ∈ values, entry.1 ↦ᵣ RVal_Bits (entry.2 : bv 64)) ∗
   reg_col predicates ∗ reg_col remaining ∗ True)%I -∗ reg_col requested.
Proof.
  intros Hperm. iIntros "(Hvalues & Hpredicates & Hremaining & _)".
  iPoseProof (reg_col_bv_list_shape with "Hvalues") as "Hknown".
  rewrite /reg_col Hperm !big_sepL_app. iFrame.
Qed.
Print Assumptions reg_col_shape_predicate.
Print Assumptions reg_col_mixed_collect.
