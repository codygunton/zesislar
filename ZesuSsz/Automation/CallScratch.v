Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma call_scratch_reuse `{!islaG Sigma}
    (sp ret : bv 64) (bytes : list (bv 8)) :
  length bytes = 32%nat ->
  (0x20000000 <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 16) ↦ₘ? 8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗ True)%I -∗
  (bv_unsigned sp - 48) ↦ₘ? 48.
Proof.
  intros Hlen Hlow. iIntros "(Hpayload & Hgap & Hret & _)".
  iDestruct (byte_array_forget with "Hpayload") as "Hpayload".
  have Haddress : bv_unsigned (sp - BV 64 48)%bv = (bv_unsigned sp - 48)%Z by bv_solve.
  iEval (rewrite Hlen Haddress /=) in "Hpayload".
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hret") as "Hret".
  iEval (cbn) in "Hret".
  iEval (replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp - 16 + 8)%Z by lia) in "Hret".
  iPoseProof (mem_mapsto_uninit_combine 8 (bv_unsigned sp - 16) (DfracOwn 1) 16
    with "Hgap Hret") as "Hrest"; first lia.
  iEval (replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp - 48 + 32)%Z by lia) in "Hrest".
  iApply (mem_mapsto_uninit_combine 32 (bv_unsigned sp - 48) (DfracOwn 1) 48
    with "Hpayload Hrest"). lia.
Qed.
Print Assumptions call_scratch_reuse.
