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
