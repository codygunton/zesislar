Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessStorageKeysSpec WriteSuccessExactStorageKeysPayloadScratch.

Lemma storage_keys_payload_scratch_at `{!islaG Sigma}
    (sp : bv 64) (key : list (bv 8)) :
  0x20000000 <= bv_unsigned sp -> bv_unsigned sp + 1744 < 0x40000000 ->
  length key = 32%nat ->
  bv_unsigned (sp + BV 64 1712)%bv ↦ₘ∗ key -∗ writeSuccessStorageKeysScratch sp.
Proof.
  intros Hlow Hhigh Hlength.
  replace (bv_unsigned (sp + BV 64 1712)%bv) with (bv_unsigned sp + 1712)%Z by bv_solve.
  iApply storage_keys_payload_scratch. exact Hlength.
Qed.
Print Assumptions storage_keys_payload_scratch_at.
