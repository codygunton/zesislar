Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.WordArrays.
Require Import isla.riscv64.riscv64.
Import WordMatching.

Lemma test_word_array_payload `{!islaG Sigma} (base : Z) (key : list (bv 8)) :
  length key = 32%nat ->
  0x20000000 <= base -> base + 32 < 0x40000000 ->
  base ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 key)) -∗
  (base + 8) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 key))) -∗
  (base + 16) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 16 key))) -∗
  (base + 24) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 key))) -∗
  (∃ _ : unit, base ↦ₘ∗ key ∗ True).
Proof.
  intros. iStartProof. iIntros "Ha Hb Hc Hd". zesu_run.
Qed.
Print Assumptions test_word_array_payload.
