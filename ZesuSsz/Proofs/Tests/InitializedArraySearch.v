Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma test_initialized_take_array_search `{!islaG Sigma} `{!threadG}
    (base : bv 64) (values : list (bv 64)) :
  length values = 74%nat ->
  bv_unsigned base + 1896 < machineRamEnd defaultMap ->
  (bv_unsigned base + 1032) ↦ₘ∗ take 69 values -∗
  find_in_context (FindMemMapsTo (bv_unsigned (base + BV 64 1104)%bv))
    (fun _ => True)%I.
Proof.
  intros Hlength Hupper. iStartProof. iIntros "Harray". zesu_run.
Qed.

Print Assumptions test_initialized_take_array_search.

Lemma test_initialized_take_array_search_skips_unrelated
    `{!islaG Sigma} `{!threadG}
    (base : Z) (values : list (bv 64)) :
  length values = 74%nat ->
  base ↦ₘ∗ take 4 values -∗
  (base + 32) ↦ₘ∗ take 69 values -∗
  find_in_context (FindMemMapsTo (base + 104)) (fun _ => True)%I.
Proof.
  intros Hlength. iStartProof. iIntros "Hfirst Hsecond". zesu_run.
Qed.

Print Assumptions test_initialized_take_array_search_skips_unrelated.

Lemma test_initialized_array_read_preparer `{!islaG Sigma} `{!threadG}
    (base : Z) (values : list (bv 64)) :
  length values = 74%nat ->
  (True%I : iProp Sigma) ⊢ (⌜(base + 1104 - (base + 1032)) `mod` 8 = 0⌝ ∗
   ∃ i : nat,
     ⌜Z.of_nat i = (base + 1104 - (base + 1032)) `div` 8⌝ ∗
     ⌜(i < length (take 69 values))%nat⌝ ∗
     ∃ Heq : 64%N = 64%N, True)%I.
Proof.
  intros Hlength. iStartProof. iIntros "_".
  zesu_prepare_initialized_array_read. done.
Qed.

Print Assumptions test_initialized_array_read_preparer.

Lemma test_initialized_take_lookup_value
    (base : Z) (values : list (bv 64)) (word : bv 64) :
  take 69 values !!
      Z.to_nat ((base + 1136 - (base + 1032)) `div` 8) = Some word ->
  word = default (BV 64 0) (values !! 13%nat).
Proof.
  intros Hlookup. zesu_normalize_initialized_array_value.
Qed.

Print Assumptions test_initialized_take_lookup_value.

Definition test_initialized_word (values : list (bv 64)) (index : nat) :=
  default (BV 64 0) (values !! index).

Lemma test_initialized_take_lookup_selector
    (base : Z) (values : list (bv 64)) (word : bv 64) :
  take 69 values !!
      Z.to_nat ((base + 1136 - (base + 1032)) `div` 8) = Some word ->
  word = test_initialized_word values 13%nat.
Proof.
  intros Hlookup. zesu_normalize_initialized_array_value.
Qed.

Print Assumptions test_initialized_take_lookup_selector.
