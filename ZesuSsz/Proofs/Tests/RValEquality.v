Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Section Tests.
Context `{!islaG Σ} `{!threadG}.
Lemma rval_bits_owned (n sp : bv 64) :
  ⌜RVal_Bits (n : bv 64) = RVal_Bits (sp - 2000)%bv⌝ -∗
  "x2" ↦ᵣ RVal_Bits (sp - 2000)%bv -∗ "x2" ↦ᵣ RVal_Bits n.
Proof. iStartProof. zesu_normalize_rval_bits_equality. iIntros "H". iExact "H". Qed.
Lemma rval_bits_implication (n expected : bv 64) (Δ : envs (iProp Σ)) :
  RVal_Bits n = RVal_Bits expected → envs_entails Δ (⌜n = expected⌝%I).
Proof. zesu_normalize_rval_bits_equality. iPureIntro. reflexivity. Qed.
Lemma val_bits_implication (n expected : bv 64) (Δ : envs (iProp Σ)) :
  Val_Bits n = Val_Bits expected → envs_entails Δ (⌜n = expected⌝%I).
Proof. zesu_normalize_rval_bits_equality. iPureIntro. reflexivity. Qed.
Lemma rval_bits_missing (x y : bv 64) : True.
Proof. Fail zesu_normalize_rval_bits_equality. exact I. Qed.
Lemma rval_bits_wrong : RVal_Bits (BV 64 1) ≠ RVal_Bits (BV 64 2).
Proof. intros Hwrong. Fail zesu_normalize_rval_bits_equality.
  apply zesu_rval_bits_injective in Hwrong. discriminate Hwrong.
Qed.
End Tests.
Print Assumptions rval_bits_owned.
