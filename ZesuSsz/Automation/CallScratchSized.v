Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma call_scratch_reuse_sized `{!islaG Sigma}
    (sp ret : bv 64) (bytes : list (bv 8)) (payload_size : N) :
  length bytes = N.to_nat payload_size ->
  (0x20000000 <= bv_unsigned sp - (Z.of_N payload_size + 16))%Z ->
  (bv_unsigned (sp - Z_to_bv 64 (Z.of_N payload_size + 16))%bv ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 16) ↦ₘ? 8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗ True)%I -∗
  (bv_unsigned sp - (Z.of_N payload_size + 16)) ↦ₘ? (Z.of_N payload_size + 16)%Z.
Proof.
  intros Hlen Hlow. iIntros "(Hpayload & Hgap & Hret & _)".
  iDestruct (byte_array_forget with "Hpayload") as "Hpayload".
  have Haddress : bv_unsigned (sp - Z_to_bv 64 (Z.of_N payload_size + 16))%bv =
    (bv_unsigned sp - (Z.of_N payload_size + 16))%Z.
  { have Hsize := N2Z.is_nonneg payload_size. bv_solve. }
  iEval (rewrite Hlen N_nat_Z Haddress /=) in "Hpayload".
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hret") as "Hret".
  iEval (cbn) in "Hret".
  iEval (replace (bv_unsigned sp - 8)%Z with (bv_unsigned sp - 16 + 8)%Z by lia) in "Hret".
  iPoseProof (mem_mapsto_uninit_combine 8 (bv_unsigned sp - 16) (DfracOwn 1) 16
    with "Hgap Hret") as "Hrest"; first lia.
  iEval (replace (bv_unsigned sp - 16)%Z with
    (bv_unsigned sp - (Z.of_N payload_size + 16) + Z.of_N payload_size)%Z by lia) in "Hrest".
  iApply (mem_mapsto_uninit_combine (Z.of_N payload_size)
    (bv_unsigned sp - (Z.of_N payload_size + 16)) (DfracOwn 1) (Z.of_N payload_size + 16)%Z
    with "Hpayload"); first lia.
  replace (Z.of_N payload_size + 16 - Z.of_N payload_size)%Z with 16%Z by lia.
  iExact "Hrest".
Qed.
Print Assumptions call_scratch_reuse_sized.
