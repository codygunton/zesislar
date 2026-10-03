Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import ZesuSsz.Automation.TypedArrayRestore.
Require Import isla.riscv64.riscv64.

Lemma typed_restore_dispatch_13
    `{!islaG Sigma} (base : Z) (values : list (bv 64)) (R : iProp Sigma) :
  length values = 69%nat ->
  (base + 8 * 14) ↦ₘ∗ drop 14 values -∗
  (base + 8 * 13) ↦ₘ (values !!! 13%nat) -∗ R -∗
  subsume (base ↦ₘ∗ take 13 values)
    (fun _ : unit => base ↦ₘ∗ values) (fun _ : unit => R).
Proof. intros Hlength. zesu_block. Qed.

Lemma typed_restore_dispatch_generic
    `{!islaG Sigma} n (base : Z) (values : list (bv n)) (index : nat)
    (R : iProp Sigma) :
  (index < length values)%nat ->
  (base + Z.of_N (n `div` 8) * Z.of_nat (S index)) ↦ₘ∗ drop (S index) values -∗
  (base + Z.of_N (n `div` 8) * Z.of_nat index) ↦ₘ (values !!! index) -∗ R -∗
  subsume (base ↦ₘ∗ take index values)
    (fun _ : unit => base ↦ₘ∗ values) (fun _ : unit => R).
Proof. intros Hbound. zesu_block. Qed.

Lemma typed_restore_dispatch_stack
    `{!islaG Sigma} (sp : bv 64) (values : list (bv 64)) (R : iProp Sigma) :
  length values = 69%nat ->
  (bv_unsigned sp + 1144) ↦ₘ∗ drop 14 values -∗
  (bv_unsigned sp + 1136) ↦ₘ (values !!! 13%nat) -∗ R -∗
  subsume ((bv_unsigned sp + 1032) ↦ₘ∗ take 13 values)
    (fun _ : unit => (bv_unsigned sp + 1032) ↦ₘ∗ values) (fun _ : unit => R).
Proof. intros Hlength. zesu_block. Qed.

Lemma typed_restore_reject_missing_word
    `{!islaG Sigma} (base : Z) : True.
Proof.
  Fail assert (Hinvalid :
    (base + 16) ↦ₘ∗ [BV 64 2] ⊢
    subsume (base ↦ₘ∗ take 1 [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => base ↦ₘ∗ [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => True%I)) by zesu_block.
  exact I.
Qed.

Lemma typed_restore_reject_wrong_word
    `{!islaG Sigma} (base : Z) : True.
Proof.
  Fail assert (Hinvalid :
    (base + 16) ↦ₘ∗ [BV 64 2] ∗ (base + 8) ↦ₘ (BV 64 2) ⊢
    subsume (base ↦ₘ∗ take 1 [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => base ↦ₘ∗ [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => True%I)) by zesu_block.
  exact I.
Qed.

Lemma typed_restore_reject_word_address
    `{!islaG Sigma} (base : Z) : True.
Proof.
  Fail assert (Hinvalid :
    (base + 16) ↦ₘ∗ [BV 64 2] ∗ (base + 32) ↦ₘ (BV 64 1) ⊢
    subsume (base ↦ₘ∗ take 1 [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => base ↦ₘ∗ [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => True%I)) by zesu_block.
  exact I.
Qed.

Lemma typed_restore_reject_suffix_address
    `{!islaG Sigma} (base : Z) : True.
Proof.
  Fail assert (Hinvalid :
    (base + 40) ↦ₘ∗ [BV 64 2] ∗ (base + 8) ↦ₘ (BV 64 1) ⊢
    subsume (base ↦ₘ∗ take 1 [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => base ↦ₘ∗ [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => True%I)) by zesu_block.
  exact I.
Qed.

Lemma typed_restore_reject_suffix_provenance
    `{!islaG Sigma} (base : Z) : True.
Proof.
  Fail assert (Hinvalid :
    (base + 16) ↦ₘ∗ drop 2 [BV 64 0; BV 64 1; BV 64 3] ∗
    (base + 8) ↦ₘ (BV 64 1) ⊢
    subsume (base ↦ₘ∗ take 1 [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => base ↦ₘ∗ [BV 64 0; BV 64 1; BV 64 2])
      (fun _ : unit => True%I)) by zesu_block.
  exact I.
Qed.

Lemma typed_restore_reject_bounds
    `{!islaG Sigma} (base : Z) (values : list (bv 64)) :
  length values = 69%nat ->
  base ↦ₘ∗ take 69 values -∗
  (base + 8 * 70) ↦ₘ∗ drop 70 values -∗
  (base + 8 * 69) ↦ₘ (BV 64 0) -∗ base ↦ₘ∗ values.
Proof.
  intros Hlength. iIntros "Hprefix Hsuffix Hword".
  Fail zesu_restore_typed_array_goal ltac:(zesu_finish_v1).
  iEval (rewrite take_ge; last lia) in "Hprefix".
  iExact "Hprefix".
Qed.

Print Assumptions typed_restore_dispatch_generic.
Print Assumptions typed_restore_dispatch_stack.

Lemma typed_restore_direct
    `{!islaG Sigma} (base : Z) (values : list (bv 64)) (R : iProp Sigma) :
  length values = 69%nat ->
  base ↦ₘ∗ take 13 values -∗
  (base + 8 * 14) ↦ₘ∗ drop 14 values -∗
  (base + 8 * 13) ↦ₘ (values !!! 13%nat) -∗ R -∗
  base ↦ₘ∗ values ∗ R.
Proof.
  intros Hlength. iIntros "Hprefix Hsuffix Hword HR".
  zesu_restore_typed_array_goal ltac:(zesu_finish_v1).
  iFrame.
Qed.
