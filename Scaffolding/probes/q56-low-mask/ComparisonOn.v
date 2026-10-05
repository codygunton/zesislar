Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.Switches.LowMask.
Open Scope Z_scope.
Lemma mask_add (value : bv 64) :
  bv_unsigned (bv_and (value + BV 64 64) (BV 64 255)) =
  bv_unsigned (Z_to_bv 8 (bv_unsigned value + 64)).
Proof. bv_solve. Qed.
