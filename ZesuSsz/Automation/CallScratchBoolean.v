Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma call_boolean_scratch_reuse `{!islaG Sigma} (sp ret : bv 64) (byte : bv 8) :
  ((bv_unsigned sp - 16) ↦ₘ? 7 ∗ (bv_unsigned sp - 9) ↦ₘ byte ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗ True)%I -∗ (bv_unsigned sp - 16) ↦ₘ? 16.
Proof.
  iIntros "(Hgap & Hbyte & Hret & _)".
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hbyte") as "Hbyte".
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hret") as "Hret".
  iEval (cbn) in "Hbyte Hret".
  iAssert ((bv_unsigned sp - 9) ↦ₘ? 9)%I with "[Hbyte Hret]" as "Htail".
  { iApply (mem_mapsto_uninit_combine 1 with "Hbyte"); first lia.
    replace (bv_unsigned sp - 9 + 1)%Z with (bv_unsigned sp - 8)%Z by lia.
    iExact "Hret". }
  iApply (mem_mapsto_uninit_combine 7 with "Hgap"); first lia.
  replace (bv_unsigned sp - 16 + 7)%Z with (bv_unsigned sp - 9)%Z by lia. iExact "Htail".
Qed.
Print Assumptions call_boolean_scratch_reuse.
