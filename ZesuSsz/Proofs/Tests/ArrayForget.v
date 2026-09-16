Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma array_forget_access_row `{!islaG Sigma} base (bytes : list (bv 8)) :
  length bytes = 40%nat ->
  base ↦ₘ∗ bytes -∗ base ↦ₘ? 40.
Proof.
  intros Hlength. rewrite -(Nat2Z.inj_iff _ _) in Hlength.
  iIntros "Hbytes". iPoseProof (byte_array_forget with "Hbytes") as "Hmemory".
  iEval (rewrite Hlength) in "Hmemory". iExact "Hmemory".
Qed.
Print Assumptions array_forget_access_row.
