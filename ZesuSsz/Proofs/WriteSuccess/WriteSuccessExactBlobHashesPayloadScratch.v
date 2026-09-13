Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessBlobHashesSpec WriteSuccessStorageKeysSpec WriteSuccessExactStorageKeysPayloadScratch.

Lemma blob_payload_scratch_at `{!islaG Sigma}
    (sp : bv 64) (key : list (bv 8)) :
  0x20000000 <= bv_unsigned sp -> bv_unsigned sp + 1712 < 0x40000000 ->
  length key = 32%nat ->
  bv_unsigned (sp + BV 64 1680)%bv ↦ₘ∗ key -∗ writeSuccessBlobHashesScratch sp.
Proof.
  intros Hlow Hhigh Hlength.
  have Hminus : bv_unsigned (sp - BV 64 32)%bv = (bv_unsigned sp - 32)%Z by bv_solve.
  have Haddress : bv_unsigned (sp + BV 64 1680)%bv =
    (bv_unsigned (sp - BV 64 32)%bv + 1712)%Z by (rewrite Hminus; bv_solve).
  iIntros "Hkey". rewrite Haddress.
  iPoseProof (storage_keys_payload_scratch (sp - BV 64 32)%bv key Hlength with "Hkey") as "Hscratch".
  iEval (unfold writeSuccessStorageKeysScratch; rewrite Hminus) in "Hscratch".
  iDestruct "Hscratch" as (a b c d) "(Ha & Hb & Hc & Hd & _)".
  iEval (unfold writeSuccessBlobHashesScratch).
  iExists a, b, c, d.
  iEval (replace (bv_unsigned sp - 32 + 1712)%Z with (bv_unsigned sp + 1680)%Z by lia) in "Ha".
  iEval (replace (bv_unsigned sp - 32 + 1720)%Z with (bv_unsigned sp + 1688)%Z by lia) in "Hb".
  iEval (replace (bv_unsigned sp - 32 + 1728)%Z with (bv_unsigned sp + 1696)%Z by lia) in "Hc".
  iEval (replace (bv_unsigned sp - 32 + 1736)%Z with (bv_unsigned sp + 1704)%Z by lia) in "Hd".
  iFrame.
Qed.
Print Assumptions blob_payload_scratch_at.
