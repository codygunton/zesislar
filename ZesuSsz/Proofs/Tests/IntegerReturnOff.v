Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Switches.ReturnRoute.
Require Import isla.riscv64.riscv64.
Open Scope Z_scope.

Lemma integerReturnOff (Sigma : gFunctors) (R : Z)
    (Haligned : (R mod 2 = 0)%Z) : True.
Proof.
  Fail assert (Henabled : ZesuStepIntegerReturn) by typeclasses eauto.
  Fail assert (Hnormalized : LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))))
    by zesu_return_integer_normalize.
  exact I.
Qed.

Lemma integerReturnFaultOff (R : Z)
    (Hrange : (0 <= R < 2 ^ 64)%Z) (Haligned : (R mod 4 = 0)%Z) : True.
Proof.
  Fail assert (Hfault : SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False)
    by zesu_return_integer_fault.
  exact I.
Qed.

Print Assumptions integerReturnOff.
Print Assumptions integerReturnFaultOff.
