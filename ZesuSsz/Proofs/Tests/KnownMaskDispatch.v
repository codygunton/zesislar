Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Lemma known_mask (b : bv 64)
    (Hmask : Z.land (bv_unsigned b) 131072 = 0%Z) :
  SHELVED_SIDECOND
    (Val_Bool (bool_decide (bv_and b 131072%bv = 0%bv)) = Val_Bool true).
Proof using All.
  pose (unrelated0 := bv_or b b).
  pose (unrelated1 := bv_or unrelated0 unrelated0).
  pose (unrelated2 := bv_or unrelated1 unrelated1).
  pose (unrelated3 := bv_or unrelated2 unrelated2).
  pose (unrelated4 := bv_or unrelated3 unrelated3).
  time zesu_finish.
Qed.
Lemma unrelated_mask_preserved (b other : bv 64)
    (Hother : Z.land (bv_unsigned other) 131072 = 0%Z) : True.
Proof using All.
  assert_fails (assert (SHELVED_SIDECOND
    (Val_Bool (bool_decide (bv_and b 131072%bv = 0%bv)) = Val_Bool true))
    by zesu_finish_known_mask).
  let observed := type of Hother in
  constr_eq observed (Z.land (bv_unsigned other) 131072 = 0%Z).
  exact I.
Qed.
Lemma known_alignment (pointer : bv 64)
    (Halign : bv_unsigned pointer mod 16 = 0%Z) :
  SHELVED_SIDECOND (bv_unsigned pointer mod 8 = 0%Z).
Proof using All. time zesu_finish. Qed.
Lemma unrelated_alignment_preserved (pointer other : bv 64)
    (Hother : bv_unsigned other mod 16 = 0%Z) : True.
Proof using All.
  assert_fails (assert (SHELVED_SIDECOND
    (bv_unsigned pointer mod 8 = 0%Z)) by zesu_finish_known_alignment).
  let observed := type of Hother in
  constr_eq observed (bv_unsigned other mod 16 = 0%Z).
  exact I.
Qed.
Print Assumptions known_alignment.
Print Assumptions unrelated_alignment_preserved.
Print Assumptions known_mask.
Print Assumptions unrelated_mask_preserved.

Require Import ZesuSsz.Automation.Switches.BoundedArithmetic.
Section byte_index.
  Context (pointer : bv 64) (base : Z) (processed remaining : nat)
    (bytes : list (bv 8)).
  Context (Hbase : (0 <= base)%Z)
    (Hram : (base + Z.of_nat (length bytes) < 1073741824)%Z)
    (Hpointer : bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z)
    (Hlength : (length bytes = 32 * (processed + S remaining))%nat).
  Lemma deferred_nonnegative : SHELVED_SIDECOND
    (0 <= (bv_unsigned (pointer + 17)%bv - base) / 1)%Z.
  Proof using All. time zesu_finish. Qed.
  Lemma deferred_index_preserves (unrelated : Prop) (Hother : unrelated) :
    SHELVED_SIDECOND
      (Z.to_nat ((bv_unsigned (pointer + 17)%bv - base) / 1) < length bytes)%nat
    /\ unrelated.
  Proof using All.
    split; [time zesu_finish | exact Hother].
  Qed.
End byte_index.
Lemma deferred_index_requires_bounds (pointer : bv 64) (base : Z)
    (bytes : list (bv 8)) (unrelated : Prop) (Hother : unrelated) : True.
Proof using All.
  assert_fails (assert (SHELVED_SIDECOND
    (Z.to_nat ((bv_unsigned (pointer + 17)%bv - base) / 1) < length bytes)%nat)
    by zesu_finish_deferred_byte_index).
  exact I.
Qed.
Print Assumptions deferred_nonnegative.
Print Assumptions deferred_index_preserves.
Print Assumptions deferred_index_requires_bounds.

Section arithmetic_disabled.
  Local Remove Hints zesu_switch_bounded_arithmetic : typeclass_instances.
  Lemma deferred_index_respects_switch (pointer : bv 64) (base : Z)
      (processed remaining : nat) (bytes : list (bv 8))
      (Hbase : (0 <= base)%Z)
      (Hram : (base + Z.of_nat (length bytes) < 1073741824)%Z)
      (Hpointer : bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z)
      (Hlength : (length bytes = 32 * (processed + S remaining))%nat) : True.
  Proof using All.
    assert_fails (assert (SHELVED_SIDECOND
      (Z.to_nat ((bv_unsigned (pointer + 17)%bv - base) / 1) < length bytes)%nat)
      by zesu_finish_deferred_byte_index).
    exact I.
  Qed.
End arithmetic_disabled.
Print Assumptions deferred_index_respects_switch.
