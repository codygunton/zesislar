Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Open Scope Z_scope.
Lemma mask_add (value : bv 64) :
  bv_unsigned (bv_and (value + BV 64 64) (BV 64 255)) =
  bv_unsigned (Z_to_bv 8 (bv_unsigned value + 64)).
Proof.
  Fail zesu_low_mask_if_enabled.
  Fail timeout 2 bv_solve.
  apply (zesu_unsigned_low_mask_add_integer 64 8 value (BV 64 255) 64).
  all: vm_compute; congruence.
Qed.
