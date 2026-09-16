Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.ArrayPacking.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessBlobHashesSpec.

Lemma blob_payload_scratch_at `{!islaG Sigma}
    (sp : bv 64) (key : list (bv 8)) :
  (mapRamBase defaultMap) <= bv_unsigned sp -> bv_unsigned sp + 1712 < (machineRamEnd defaultMap) ->
  length key = 32%nat ->
  bv_unsigned (sp + BV 64 1680)%bv ↦ₘ∗ key -∗ writeSuccessBlobHashesScratch sp.
Proof.
  intros Hlow Hhigh Hlength.
  have Haddress : bv_unsigned (sp + BV 64 1680)%bv =
    (bv_unsigned sp + 1680)%Z by bv_solve.
  iIntros "Hkey". iEval (rewrite Haddress) in "Hkey".
  iDestruct (zesu_bytes32_four_words (bv_unsigned sp + 1680) key Hlength
    with "Hkey") as (a b c d) "(Ha & Hb & Hc & Hd)".
  unfold writeSuccessBlobHashesScratch. iExists a, b, c, d.
  iEval (replace (bv_unsigned sp + 1680 + 8)%Z with (bv_unsigned sp + 1688)%Z by lia) in "Hb".
  iEval (replace (bv_unsigned sp + 1680 + 16)%Z with (bv_unsigned sp + 1696)%Z by lia) in "Hc".
  iEval (replace (bv_unsigned sp + 1680 + 24)%Z with (bv_unsigned sp + 1704)%Z by lia) in "Hd".
  iFrame.
Qed.
Print Assumptions blob_payload_scratch_at.
