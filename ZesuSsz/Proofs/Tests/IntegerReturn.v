Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ReturnRoute.
Require Import ZesuSsz.Automation.Switches.IntegerReturn.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Open Scope Z_scope.

Definition return_integer_rule (Sigma : gFunctors) (R : Z)
    (Haligned : (R mod 2 = 0)%Z) :
  LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))).
Proof. zesu_return_integer_normalize. Defined.

Lemma return_integer_continuation (Sigma : gFunctors) (R : Z)
    (Haligned : (R mod 2 = 0)%Z) (T : Z -> iProp Sigma) :
  li_tactic_P (return_integer_rule Sigma R Haligned) T = T R.
Proof. reflexivity. Qed.

Lemma return_integer_alias (Sigma : gFunctors) (R : Z)
    (Haligned : (R mod 4 = 0)%Z) :
  LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))).
Proof.
  pose (savedReturn := Z_to_bv 64 R).
  change (LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add savedReturn (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0))))).
  zesu_return_integer_normalize.
Qed.

Lemma return_integer_missing_alignment (Sigma : gFunctors) (R : Z) : True.
Proof.
  Fail assert (Hbad : LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))))
    by zesu_return_integer_normalize.
  exact I.
Qed.

Lemma return_integer_odd (Sigma : gFunctors) (R : Z)
    (Hodd : (R mod 2 = 1)%Z) : True.
Proof.
  Fail assert (Hbad : LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))))
    by zesu_return_integer_normalize.
  exact I.
Qed.

Lemma return_integer_unrelated (Sigma : gFunctors) (R : Z)
    (Haligned : (R mod 4 = 0)%Z) : True.
Proof.
  Fail assert (Hbad : LiTactic (normalize_instr_addr (Σ:=Sigma) R))
    by zesu_return_integer_normalize.
  exact I.
Qed.

Print Assumptions return_integer_rule.
Print Assumptions return_integer_continuation.
Print Assumptions return_integer_alias.

Lemma return_integer_fault (R : Z)
    (Hrange : (0 <= R < 2 ^ 64)%Z) (Haligned : (R mod 4 = 0)%Z) :
  SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False.
Proof. zesu_return_integer_fault. Qed.

Lemma return_integer_fault_missing_alignment (R : Z)
    (Hrange : (0 <= R < 2 ^ 64)%Z) : True.
Proof.
  Fail assert (Hbad : SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False)
    by zesu_return_integer_fault.
  exact I.
Qed.

Print Assumptions return_integer_fault.

Lemma return_integer_fault_misaligned (R : Z)
    (Hrange : (0 <= R < 2 ^ 64)%Z) (Hmisaligned : (R mod 4 = 2)%Z) : True.
Proof.
  Fail assert (Hbad : SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False)
    by zesu_return_integer_fault.
  exact I.
Qed.
Print Assumptions return_integer_fault_misaligned.

Lemma return_integer_misaligned (Sigma : gFunctors) (R : Z)
    (Hrange : (0 <= R < 2 ^ 64)%Z) (Hmisaligned : (R mod 4 = 2)%Z) : True.
Proof.
  Fail assert (Hbad : LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))))
    by zesu_return_integer_normalize.
  exact I.
Qed.
Print Assumptions return_integer_misaligned.
