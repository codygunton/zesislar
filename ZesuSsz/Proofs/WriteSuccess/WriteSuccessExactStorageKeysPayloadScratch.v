Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessStorageKeysSpec WriteSuccessExactStorageKeysResources.

Lemma storage_keys_payload_scratch `{!islaG Sigma}
    (sp : bv 64) (key : list (bv 8)) :
  length key = 32%nat ->
  (bv_unsigned sp + 1712) ↦ₘ∗ key -∗ writeSuccessStorageKeysScratch sp.
Proof.
  intros Hlength. iIntros "Hkey".
  iPoseProof (storage_keys_bytes_four_words (bv_unsigned sp + 1712)
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 key)))
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 key))))
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 16 key))))
    (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 key))))
    with "[Hkey]") as "Hwords".
  { rewrite (storage_keys_packed_payload key Hlength). iExact "Hkey". }
  iDestruct "Hwords" as "(Ha & Hb & Hc & Hd)".
  iEval (replace (bv_unsigned sp + 1712 + 8)%Z with (bv_unsigned sp + 1720)%Z by lia) in "Hb".
  iEval (replace (bv_unsigned sp + 1712 + 16)%Z with (bv_unsigned sp + 1728)%Z by lia) in "Hc".
  iEval (replace (bv_unsigned sp + 1712 + 24)%Z with (bv_unsigned sp + 1736)%Z by lia) in "Hd".
  iEval (unfold writeSuccessStorageKeysScratch).
  iExists _, _, _, _. iFrame.
Qed.
Print Assumptions storage_keys_payload_scratch.
