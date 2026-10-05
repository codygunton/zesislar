Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Open Scope Z_scope.
Lemma audit_aliases (prefix : bv 64) :
  let LET0 := (prefix + BV 64 64)%bv in
  let LET2 := bv_and LET0 (BV 64 255) in
  bv_unsigned LET2 = bv_unsigned (Z_to_bv 8 (bv_unsigned prefix + 64)).
Proof.
  intros LET0 LET2.
  Fail zesu_low_mask_if_enabled.
  Fail timeout 2 bv_solve.
  apply (zesu_unsigned_low_mask_add_integer 64 8 prefix (BV 64 255) 64).
  all: vm_compute; congruence.
Qed.
