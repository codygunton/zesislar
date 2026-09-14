Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayForget.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma call_bytes_scratch_reuse `{!islaG Sigma}
    (sp ret countret stack2 old9 old8 : bv 64) (bytes : list (bv 8)) :
  length bytes = 8%nat -> ((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 40) ↦ₘ countret ∗ (bv_unsigned sp - 32) ↦ₘ stack2 ∗
   (bv_unsigned sp - 24) ↦ₘ old9 ∗ (bv_unsigned sp - 16) ↦ₘ old8 ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗ True)%I -∗ (bv_unsigned sp - 48) ↦ₘ? 48.
Proof.
  intros Hlen Hlow. iIntros "(Hbytes & H0 & H1 & H2 & H3 & H4 & _)".
  iDestruct (byte_array_forget with "Hbytes") as "Hbytes".
  have Haddress : bv_unsigned (sp - BV 64 48)%bv = bv_unsigned sp - 48.
  { clear -Hlow. bv_solve. }
  iEval (rewrite Hlen Haddress /=) in "Hbytes".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H0") as "H0".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H1") as "H1".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H2") as "H2".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H3") as "H3".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H4") as "H4".
  iEval (cbn) in "H0 H1 H2 H3 H4".
  iApply (mem_mapsto_uninit_combine 8 with "Hbytes"); first lia.
  replace (bv_unsigned sp - 48 + 8)%Z with (bv_unsigned sp - 40)%Z by lia.
  iApply (mem_mapsto_uninit_combine 8 with "H0"); first lia.
  replace (bv_unsigned sp - 40 + 8)%Z with (bv_unsigned sp - 32)%Z by lia.
  iApply (mem_mapsto_uninit_combine 8 with "H1"); first lia.
  replace (bv_unsigned sp - 32 + 8)%Z with (bv_unsigned sp - 24)%Z by lia.
  iApply (mem_mapsto_uninit_combine 8 with "H2"); first lia.
  replace (bv_unsigned sp - 24 + 8)%Z with (bv_unsigned sp - 16)%Z by lia.
  iApply (mem_mapsto_uninit_combine 8 with "H3"); first lia.
  replace (bv_unsigned sp - 16 + 8)%Z with (bv_unsigned sp - 8)%Z by lia.
  iExact "H4".
Qed.
Print Assumptions call_bytes_scratch_reuse.
