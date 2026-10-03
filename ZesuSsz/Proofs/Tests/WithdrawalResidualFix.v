Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import ZesuSsz.Automation.Finish.
Require Import ZesuSsz.Automation.PackedWordValues.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.

Lemma reverse_u64_default (values : list (bv 64)) :
  default (BV 64 0) (take 69 values !! 13%nat) = take 69 values !!! 13%nat.
Proof. zesu_finish_u64_lookup_symmetric. Qed.

Lemma trace_u64_nested `{!islaG Sigma} (values : list (bv 64)) :
  True -∗ (∃ x : li_prod spec unit,
    ⌜take 69 values !!! 13%nat = default (BV 64 0) (take 69 values !! 13%nat)⌝ ∗ True : iProp Sigma).
Proof.
  iIntros "_". zesu_trace_u64_lookup_normalize (16%nat).
  iExists ((fun _ : list seq_label => False), tt)ₗ.
  iSplit; first (iPureIntro; reflexivity). done.
Qed.

Lemma scalar_index_after_restore `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) :
  (bv_unsigned sp + 1144) ↦ₘ
    (take 69 values !!! array_region_start 64 (bv_unsigned sp + 1032)
       (bv_unsigned sp + 1144)) -∗
  ((bv_unsigned sp + 1032 + 8 * array_region_start 64
      (bv_unsigned sp + 1032) (bv_unsigned sp + 1144)) ↦ₘ
    (take 69 values !!! array_region_start 64 (bv_unsigned sp + 1032)
       (bv_unsigned sp + 1144)) ∗ True).
Proof. iIntros "Hword". zesu_run. Qed.
Print Assumptions reverse_u64_default.
Print Assumptions trace_u64_nested.
Print Assumptions scalar_index_after_restore.
