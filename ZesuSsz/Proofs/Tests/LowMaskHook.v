Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Open Scope Z_scope.

Lemma low_mask_disabled (value : bv 64) :
  bv_unsigned (bv_and (value + BV 64 64) (BV 64 255)) =
  bv_unsigned (Z_to_bv 8 (bv_unsigned value + 64)).
Proof.
  Fail zesu_low_mask_if_enabled.
  apply (zesu_unsigned_low_mask_add_integer 64 8 value (BV 64 255) 64).
  all: vm_compute; congruence.
Qed.

Section enabled.
  Local Instance low_mask_enabled : ZesuStepLowMask := I.

  Lemma low_mask_byte_add (value : bv 64) :
    bv_unsigned (bv_and (value + BV 64 64) (BV 64 255)) =
    bv_unsigned (Z_to_bv 8 (bv_unsigned value + 64)).
  Proof. zesu_low_mask_if_enabled. Qed.

  Lemma low_mask_audit_aliases (prefix : bv 64) :
    let LET0 := (prefix + BV 64 64)%bv in
    let LET2 := bv_and LET0 (BV 64 255) in
    bv_unsigned LET2 = bv_unsigned (Z_to_bv 8 (bv_unsigned prefix + 64)).
  Proof. intros LET0 LET2. bv_solve. Qed.

  Lemma low_mask_halfword_wrap (value : bv 32) :
    bv_unsigned (bv_and (value + BV 32 65536) (BV 32 65535)) =
    bv_unsigned (Z_to_bv 16 (bv_unsigned value + 65536)).
  Proof. zesu_low_mask_if_enabled. Qed.

  Lemma low_mask_negative_offset (value : bv 64) :
    bv_unsigned (bv_and (value + Z_to_bv 64 (-73)) (BV 64 255)) =
    bv_unsigned (Z_to_bv 8 (bv_unsigned value - 73)).
  Proof.
    change (bv_unsigned (bv_and (value + Z_to_bv 64 (-73)) (BV 64 255)) =
      bv_unsigned (Z_to_bv 8 (bv_unsigned value + -73))).
    zesu_low_mask_if_enabled.
  Qed.

  Lemma low_mask_symbolic_integer (value : bv 64) (offset : Z) :
    bv_unsigned (bv_and (value + Z_to_bv 64 offset) (BV 64 255)) =
    bv_unsigned (Z_to_bv 8 (bv_unsigned value + offset)).
  Proof. zesu_low_mask_if_enabled. Qed.

  Lemma low_mask_symbolic_bitvector (value offset : bv 32) :
    bv_unsigned (bv_and (value + offset) (BV 32 65535)) =
    bv_unsigned (Z_to_bv 16 (bv_unsigned value + bv_unsigned offset)).
  Proof. zesu_low_mask_if_enabled. Qed.

  Lemma low_mask_solver_integration (value : bv 64) :
    bv_unsigned (bv_and (value + BV 64 64) (BV 64 255)) =
    bv_unsigned (Z_to_bv 8 (bv_unsigned value + 64)).
  Proof. bv_solve. Qed.

  Lemma low_mask_wrong_mask (value : bv 64)
      (Hsame : bv_unsigned (bv_and (value + BV 64 64) (BV 64 254)) =
        bv_unsigned (Z_to_bv 8 (bv_unsigned value + 64))) :
    bv_unsigned (bv_and (value + BV 64 64) (BV 64 254)) =
    bv_unsigned (Z_to_bv 8 (bv_unsigned value + 64)).
  Proof. Fail zesu_low_mask_if_enabled. exact Hsame. Qed.

  Lemma low_mask_wrong_width (value : bv 8)
      (Hsame : bv_unsigned (bv_and (value + Z_to_bv 8 256) (BV 8 255)) =
        bv_unsigned (Z_to_bv 16 (bv_unsigned value + 256))) :
    bv_unsigned (bv_and (value + Z_to_bv 8 256) (BV 8 255)) =
    bv_unsigned (Z_to_bv 16 (bv_unsigned value + 256)).
  Proof. Fail zesu_low_mask_if_enabled. exact Hsame. Qed.
End enabled.
