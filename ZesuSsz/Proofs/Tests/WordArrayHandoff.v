Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma word_array_handoff_is_opt_in : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepWordArrayHandoff) in idtac.
  exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.WordArrayHandoff.

Definition handoff_test_width : Z := 16.

Lemma word_array_handoff_closed_terms (address : Z) : True.
Proof.
  Fail zesu_handoff_closed_term address.
  Fail zesu_handoff_closed_term (fun _ : nat => address).
  zesu_handoff_closed_term handoff_test_width.
  exact I.
Qed.

Lemma word_array_handoff_hidden_width `{!islaG Sigma}
    (address : Z) (low high : bv 64) :
  (address + -16 + 0) ↦ₘ low -∗
  (address + -16 + 8) ↦ₘ high -∗
  (address - handoff_test_width) ↦ₘ?
    (address + -16 + 0 - (address - handoff_test_width)) -∗
  ∃ bytes : list (bv 8),
    (address - handoff_test_width) ↦ₘ∗ bytes ∗
    ⌜bytes = bv_to_little_endian 8 8 (bv_unsigned low) ++
      bv_to_little_endian 8 8 (bv_unsigned high)⌝ ∗ True.
Proof.
  iStartProof.
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"].
  zesu_run.
Qed.

Lemma word_array_handoff_positive_offset `{!islaG Sigma}
    (address : Z) (low high : bv 64) :
  (address + 5) ↦ₘ low -∗ (address + 13) ↦ₘ high -∗
  ∃ bytes : list (bv 8), (address + 5) ↦ₘ∗ bytes ∗
    ⌜bytes = bv_to_little_endian 8 8 (bv_unsigned low) ++
      bv_to_little_endian 8 8 (bv_unsigned high)⌝ ∗ True.
Proof.
  iStartProof.
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"].
  zesu_run.
Qed.

Print Assumptions word_array_handoff_hidden_width.
Print Assumptions word_array_handoff_positive_offset.


Lemma word_array_handoff_empty_keeps_bounds `{!islaG Sigma}
    (address : Z) :
  address ↦ₘ? (handoff_test_width - 16) -∗ ⌜0 ≤ address ≤ 2 ^ 64⌝.
Proof.
  iStartProof.
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"].
  zesu_run.
Qed.

Print Assumptions word_array_handoff_empty_keeps_bounds.

Lemma word_array_handoff_wrapped_subtraction (address : Z) :
  (Z_to_bv 64 address + Z_to_bv 64 (- handoff_test_width))%bv =
    Z_to_bv 64 (address - handoff_test_width).
Proof.
  exact (zesu_Z_to_bv_add 64 address (- handoff_test_width)).
Qed.

Print Assumptions word_array_handoff_wrapped_subtraction.
