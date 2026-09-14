Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArraySlices.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Import SliceMatching.

Lemma test_array_slice_stack_index (sp : bv 64) :
  bv_unsigned sp + 1784 < (machineRamEnd defaultMap) ->
  array_region_start 8 (bv_unsigned (sp + BV 64 1744)%bv)
    (bv_unsigned (sp + BV 64 1760)%bv) = 16%nat.
Proof.
  intros. rewrite array_slice_stack_index; [reflexivity | bv_solve | bv_solve].
Qed.
Print Assumptions test_array_slice_stack_index.

Lemma test_array_slice_preserves_sides `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 40%nat ->
  base ↦ₘ∗ bytes -∗
  (base ↦ₘ∗ take 16 bytes ∗
   (base + 16) ↦ₘ∗ take 20 (drop 16 bytes) ∗
   (base + 36) ↦ₘ∗ drop 36 bytes).
Proof.
  intros Hlength. iIntros "Hbytes".
  iDestruct (subsume_mem_array_slice unit base (base + 16) bytes 16 20
    (fun _ => (base ↦ₘ∗ take 16 bytes ∗ (base + 36) ↦ₘ∗ drop 36 bytes)%I)
    with "[] Hbytes") as (x) "[Hslice [Hprefix Hsuffix]]".
  { iSplit; [done |]. iSplit; [iPureIntro; lia |].
    iIntros "Hprefix Hsuffix". iExists tt. iFrame. }
  iFrame.
Qed.
Print Assumptions test_array_slice_preserves_sides.

Lemma test_array_slice_matching `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 40%nat ->
  base ↦ₘ∗ bytes -∗
  (∃ _ : unit, (base + 16) ↦ₘ∗ take 20 (drop 16 bytes) ∗
    base ↦ₘ∗ take 16 bytes ∗ (base + 36) ↦ₘ∗ drop 36 bytes).
Proof.
  intros Hlength. iStartProof. iIntros "Hbytes". zesu_run.
Qed.
Print Assumptions test_array_slice_matching.
