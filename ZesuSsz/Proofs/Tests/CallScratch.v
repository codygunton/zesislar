Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CallScratch.
Require Import isla.riscv64.riscv64.

Lemma call_scratch_keeps_external_bytes `{!islaG Sigma}
    (sp ret : bv 64) (bytes : list (bv 8))
    (externalBase : Z) (externalBytes : list (bv 8)) :
  length bytes = 32%nat ->
  ((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 16) ↦ₘ? 8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   externalBase ↦ₘ∗ externalBytes ∗ True)%I -∗
  ((bv_unsigned sp - 48) ↦ₘ? 48 ∗ externalBase ↦ₘ∗ externalBytes ∗ True)%I.
Proof.
  intros Hlen Hlow. iIntros "(Hpayload & Hgap & Hret & Hexternal & _)".
  iFrame "Hexternal".
  iApply (call_scratch_reuse sp ret bytes Hlen Hlow with "[$Hpayload $Hgap $Hret]").
Qed.
Print Assumptions call_scratch_keeps_external_bytes.
