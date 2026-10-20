Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ReturnRoute.
Require Import ZesuSsz.Automation.Switches.IntegerReturn.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
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

Lemma return_integer_mask_alias (Sigma : gFunctors) (R : Z)
    (Haligned : (R mod 2 = 0)%Z) :
  LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))).
Proof.
  pose (maskedReturn := bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
    (BV 64 0xfffffffffffffffe)) (BV 64 0)).
  change (LiTactic (normalize_instr_addr (Σ:=Sigma) (bv_unsigned maskedReturn))).
  Fail lazymatch goal with
  | |- LiTactic (normalize_instr_addr (bv_unsigned (bv_or (bv_and _ _) _))) => idtac
  end.
  zesu_return_integer_normalize.
Qed.

Lemma return_integer_fault_mask_alias (R : Z)
    (Hrange : (0 <= R < 2 ^ 64)%Z) (Haligned : (R mod 4 = 0)%Z) :
  SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False.
Proof.
  pose (maskedReturn := bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
    (BV 64 18446744073709551614)) (BV 64 0)).
  change (SimplImpl
    (bv_extract 0 1 (bv_shiftr maskedReturn (BV 64 1)) = BV 1 1) False).
  zesu_return_integer_fault.
Qed.

Lemma return_integer_literal_guard (Sigma : gFunctors) : True.
Proof.
  Fail assert (Hbad : LiTactic (normalize_instr_addr (Σ:=Sigma) 42))
    by zesu_return_integer_normalize.
  Fail assert (Hbad : LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (BV 64 42)))) by zesu_return_integer_normalize.
  pose (literalReturn := BV 64 42).
  Fail zesu_return_masked_head literalReturn.
  exact I.
Qed.

Print Assumptions return_integer_mask_alias.
Print Assumptions return_integer_fault_mask_alias.
Print Assumptions return_integer_literal_guard.

Lemma bit_alias_69b0 (args : DecodeItemArgs)
  (Hrange : (0 <= decodeItemReturnAddress args < 2 ^ 64)%Z)
  (Haligned : (decodeItemReturnAddress args mod 4 = 0)%Z) : True.
Proof.
  pose (LET33 := bv_or (bv_and (bv_add (Z_to_bv 64 (decodeItemReturnAddress args)) (BV 64 0))
    (BV 64 18446744073709551614)) (BV 64 0)).
  pose (LET34 := bv_extract 0 1 (bv_shiftr LET33 (BV 64 1))).
  Fail assert (Hraw : SimplImpl (LET34 = BV 1 1) False) by
    lazymatch goal with
    | |- SimplImpl (bv_extract 0 1 (bv_shiftr _ _) = _) _ => idtac
    end.
  let inspected := eval cbv delta [LET34] in LET34 in
  lazymatch inspected with
  | bv_extract 0 1 (bv_shiftr ?selected _) => constr_eq selected LET33
  end.
  zesu_return_fault_bit_head LET34.
  is_var LET34. is_var LET33.
  assert (Hguarded : SimplImpl (LET34 = BV 1 1) False) by zesu_return_integer_fault.
  exact I.
Qed.
Print Assumptions bit_alias_69b0.

Lemma bit_alias_6a78 (args : DecodeItemArgs)
  (Hrange : (0 <= decodeItemReturnAddress args < 2 ^ 64)%Z)
  (Haligned : (decodeItemReturnAddress args mod 4 = 0)%Z) : True.
Proof.
  pose (LET38 := bv_or (bv_and (bv_add (Z_to_bv 64 (decodeItemReturnAddress args)) (BV 64 0))
    (BV 64 18446744073709551614)) (BV 64 0)).
  pose (LET39 := bv_extract 0 1 (bv_shiftr LET38 (BV 64 1))).
  Fail assert (Hraw : SimplImpl (LET39 = BV 1 1) False) by
    lazymatch goal with
    | |- SimplImpl (bv_extract 0 1 (bv_shiftr _ _) = _) _ => idtac
    end.
  let inspected := eval cbv delta [LET39] in LET39 in
  lazymatch inspected with
  | bv_extract 0 1 (bv_shiftr ?selected _) => constr_eq selected LET38
  end.
  zesu_return_fault_bit_head LET39.
  is_var LET39. is_var LET38.
  assert (Hguarded : SimplImpl (LET39 = BV 1 1) False) by zesu_return_integer_fault.
  exact I.
Qed.
Print Assumptions bit_alias_6a78.
