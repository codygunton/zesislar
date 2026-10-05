Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.

Lemma strict_signed_disabled (x y : bv 64)
    (Hlt : bv_unsigned x < bv_unsigned y) :
  bv_signed (bv_zero_extend 128 x) < bv_signed (bv_zero_extend 128 y).
Proof.
  Fail zesu_strict_signed_if_enabled.
  exact (zesu_unsigned_lt_signed_zero_extend_64_128 x y Hlt).
Qed.

Require Import ZesuSsz.Automation.Switches.StrictSigned.

Lemma strict_signed_enabled (x y : bv 64)
    (Hlt : bv_unsigned x < bv_unsigned y) :
  bv_signed (bv_zero_extend 128 x) < bv_signed (bv_zero_extend 128 y).
Proof. bv_solve. Qed.

Lemma strict_signed_aliases (x y : bv 64)
    (Hlt : bv_unsigned x < bv_unsigned y) :
  let LET0 := y in
  bv_signed (bv_zero_extend 128 x) < bv_signed (bv_zero_extend 128 LET0).
Proof. intro LET0. bv_solve. Qed.

Lemma strict_signed_reject_missing_order (x y : bv 64) : True.
Proof.
  assert_fails (assert (bv_signed (bv_zero_extend 128 x) <
    bv_signed (bv_zero_extend 128 y)) by zesu_strict_signed_if_enabled).
  exact I.
Qed.

Lemma strict_signed_reject_other_width (x y : bv 32)
    (Hlt : bv_unsigned x < bv_unsigned y) : True.
Proof.
  assert_fails (assert (bv_signed (bv_zero_extend 128 x) <
    bv_signed (bv_zero_extend 128 y)) by zesu_strict_signed_if_enabled).
  exact I.
Qed.
