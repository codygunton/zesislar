Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.WrappedWord.
Require Import isla.riscv64.riscv64.
Local Open Scope Z_scope.

Lemma zesu_wrapped_boolean_bounds (base : Z) :
  16 <= base < bv_modulus 64 ->
  bool_decide (0 <= bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8)) &&
  bool_decide (bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8) < bv_modulus 64) = true.
Proof.
  intros [Hlower Hupper].
  apply andb_true_iff; split; apply bool_decide_eq_true_2;
    zesu_wrapped_word_range ltac:(cbv [bv_unsigned bv_modulus] in *; lia).
Qed.

Lemma zesu_wrapped_owned_lookup `{!islaG Sigma} `{!threadG} (base : Z) :
  16 <= base < bv_modulus 64 ->
  (base - 16) ↦ₘ? 16 -∗
  find_in_context
    (FindMemMapsTo (bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8)))
    (fun _ => True%I).
Proof.
  intros Hrange. iIntros "Hframe".
  zesu_wrapped_memory_lookup.
  liStep.
Qed.

Print Assumptions zesu_wrapped_boolean_bounds.
Print Assumptions zesu_wrapped_owned_lookup.

Lemma zesu_wrapped_boolean_bounds_direct (base : Z) :
  16 <= base < bv_modulus 64 ->
  bool_decide (0 <= bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8)) &&
  bool_decide (bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8) < bv_modulus 64) = true.
Proof.
  intros [Hlower Hupper].
  zesu_wrapped_word_range ltac:(cbv [bv_unsigned bv_modulus] in *; lia).
Qed.

Lemma zesu_wrapped_symbolic_offset_refusal (base offset : Z) : True.
Proof.
  Fail assert (Hunsupported :
    bool_decide (0 <= bv_unsigned (Z_to_bv 64 base + Z_to_bv 64 offset + 8)) &&
    bool_decide (bv_unsigned (Z_to_bv 64 base + Z_to_bv 64 offset + 8) < bv_modulus 64) = true)
    by (zesu_wrapped_word_range ltac:(cbv [bv_unsigned bv_modulus] in *; lia)).
  exact I.
Qed.

Lemma zesu_wrapped_missing_range_refusal (base : Z) : True.
Proof.
  Fail assert (Hunsupported :
    bool_decide (0 <= bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8)) &&
    bool_decide (bv_unsigned (Z_to_bv 64 base + 18446744073709551600 + 8) < bv_modulus 64) = true)
    by (zesu_wrapped_word_range ltac:(cbv [bv_unsigned bv_modulus] in *; lia)).
  exact I.
Qed.

Print Assumptions zesu_wrapped_boolean_bounds_direct.
Print Assumptions zesu_wrapped_symbolic_offset_refusal.
Print Assumptions zesu_wrapped_missing_range_refusal.
