Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.EntryIntro.

Lemma r1b_mask_disabled (value : bv 64) (Hrange : 256 <= bv_unsigned value + 73 < 512) : True.
Proof.
  assert_fails (assert (candidate : bv_unsigned (bv_and (value + 73) 255) = bv_unsigned value - 183) by zesu_low_mask_sub_modulus_if_enabled). exact I.
Qed.

Require Import ZesuSsz.Automation.Switches.MaskNormalizer.

Lemma r1b_mask_literal73 (value : bv 64) (prefix : Z)
    (Hvalue : bv_unsigned value = prefix) (Hrange : 183 <= prefix < 256) :
    bv_unsigned (bv_and (value + 73) 255) = prefix - 183.
Proof.
  zesu_low_mask_sub_modulus_if_enabled.
Qed.

Lemma r1b_mask_literal9 (value : bv 64) (prefix : Z)
    (Hvalue : bv_unsigned value = prefix) (Hrange : 247 <= prefix < 256) :
    bv_unsigned (bv_and (value + 9) 255) = prefix - 247.
Proof.
  zesu_low_mask_sub_modulus_if_enabled.
Qed.

Lemma r1b_mask_missing_range (value : bv 64) : True.
Proof.
  assert_fails (assert (candidate : bv_unsigned (bv_and (value + 73) 255) = bv_unsigned value - 183) by zesu_low_mask_sub_modulus_if_enabled). exact I.
Qed.

Lemma r1b_mask_wrong_mask (value : bv 64) (Hrange : 256 <= bv_unsigned value + 73 < 512) : True.
Proof.
  assert_fails (assert (candidate : bv_unsigned (bv_and (value + 73) 254) = bv_unsigned value - 183) by zesu_low_mask_sub_modulus_if_enabled). exact I.
Qed.

Lemma r1b_mask_symbolic_mask (value mask : bv 64) (Hrange : 256 <= bv_unsigned value + 73 < 512) : True.
Proof.
  assert_fails (assert (candidate : bv_unsigned (bv_and (value + 73) mask) = bv_unsigned value - 183) by zesu_low_mask_sub_modulus_if_enabled). exact I.
Qed.

Lemma r1b_mask_outside_range (value : bv 64) (Hrange : bv_unsigned value + 73 < 256) : True.
Proof.
  assert_fails (assert (candidate : bv_unsigned (bv_and (value + 73) 255) = bv_unsigned value - 183) by zesu_low_mask_sub_modulus_if_enabled). exact I.
Qed.

Lemma r1b_mask_width8 (value : bv 8) (prefix : Z)
    (Hvalue : bv_unsigned value = prefix) (Hrange : 13 <= prefix < 16) :
    bv_unsigned (bv_and (value + 3) 15) = prefix - 13.
Proof.
  zesu_low_mask_sub_modulus_if_enabled.
Qed.

Lemma r1b_mask_width0 (value : bv 0) (offset : Z)
    (Hrange : 1 <= bv_unsigned value + offset < 2) :
    bv_unsigned (bv_and (value + Z_to_bv 0 offset) 0) = bv_unsigned value + offset - 1.
Proof.
  zesu_low_mask_sub_modulus_if_enabled.
Qed.

Lemma r1b_mask_upper_range (value : bv 64) (Hrange : 512 <= bv_unsigned value + 73) : True.
Proof.
  assert_fails (assert (candidate : bv_unsigned (bv_and (value + 73) 255) = bv_unsigned value - 183) by zesu_low_mask_sub_modulus_if_enabled). exact I.
Qed.

Lemma r1b_mask_branch73 (value limit : bv 64) (prefix : Z)
    (Hvalue : bv_unsigned value = prefix) (Hrange : 184 <= prefix <= 191)
    (Hguard : ~ bv_signed (bv_zero_extend 128 (bv_and (value + 73) 255)) >=
      bv_signed (bv_zero_extend 128 limit)) :
    prefix - 183 < bv_unsigned limit.
Proof. zesu_low_mask_sub_modulus_if_enabled. Qed.

Lemma r1b_mask_branch9 (value limit : bv 64) (prefix : Z)
    (Hvalue : bv_unsigned value = prefix) (Hrange : 248 <= prefix <= 255)
    (Hguard : ~ bv_signed (bv_zero_extend 128 (bv_and (value + 9) 255)) >=
      bv_signed (bv_zero_extend 128 limit)) :
    prefix - 247 < bv_unsigned limit.
Proof. zesu_low_mask_sub_modulus_if_enabled. Qed.

Lemma r1b_mask_branch_missing_range (value limit : bv 64)
    (Hguard : ~ bv_signed (bv_zero_extend 128 (bv_and (value + 73) 255)) >=
      bv_signed (bv_zero_extend 128 limit)) : True.
Proof.
  assert_fails (assert (candidate : bv_unsigned value - 183 < bv_unsigned limit)
    by zesu_low_mask_sub_modulus_if_enabled). exact I.
Qed.

Lemma r1b_prime_Z (value : bv 64) (prefix offset : Z)
    (Hvalue : bv_unsigned value = prefix)
    (Hrange : 256 <= prefix + offset < 512) :
    bv_unsigned (bv_and (value + Z_to_bv 64 offset) 255) = prefix + offset - 256.
Proof. zesu_low_mask_sub_modulus_if_enabled. Qed.

Lemma r1b_prime_bv (value : bv 64) (prefix offset : Z)
    (Hvalue : bv_unsigned value = prefix)
    (Hrange : 256 <= prefix + offset < 512) :
    bv_and (value + Z_to_bv 64 offset) 255 = Z_to_bv 64 (prefix + offset - 256).
Proof. zesu_low_mask_sub_modulus_if_enabled. Qed.
