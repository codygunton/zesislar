Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.Switches.LowMask.
Open Scope Z_scope.
Lemma audit_aliases (prefix : bv 64) :
  let LET0 := (prefix + BV 64 64)%bv in
  let LET2 := bv_and LET0 (BV 64 255) in
  bv_unsigned LET2 = bv_unsigned (Z_to_bv 8 (bv_unsigned prefix + 64)).
Proof. intros LET0 LET2. bv_solve. Qed.
