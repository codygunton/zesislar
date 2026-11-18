Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

#[local] Instance integer_return_enabled :
  ZesuSsz.Automation2.IntegerReturn.ZesuStepIntegerReturn := I.

(* A function's folded precondition: a domain predicate whose body is a tree
   of conjunctions stating the return target's range and alignment. *)
Definition target_domain (R : Z) : Prop :=
  (0 <= R /\ R < 2 ^ 64) /\ R mod 4 = 0.

(* The same tree without the alignment conjunct. *)
Definition target_range (R : Z) : Prop := 0 <= R /\ R < 2 ^ 64.

(* A generated precondition can state the bound as a literal and the
   alignment modulus as a product. Opening the tree (the integer facts
   before the folded branch already do) then exposes facts that differ from
   the requested ones by computation only, which a syntactic match misses. *)
Definition target_domain_constants (R : Z) : Prop :=
  (0 <= R /\ R < 18446744073709551616) /\ R mod (2 * 2) = 0.

(* The finisher alternatives before the return-target bit rule. *)
Ltac previous_finish_lia :=
  first [ZesuSsz.Automation2.LoopBackedgeJoin.zesu_loop_pure_finish | solve [ZesuSsz.Automation2.MaskWitness.zesu_mask_fact_close] |
    (zesu_linear_goal_shape; zesu_solve_machine_linear) | solve [ZesuSsz.Automation2.FlagMaskBounds.zesu_flag_mask_bound] |
    solve [ZesuSsz.Automation2.Hooks.zesu_flag_mask_bound_derived]].

(* Bit 1 of a return target whose word is aligned to four. *)
Lemma target_bit_word (value : bv 64) (Haligned : bv_unsigned value mod 4 = 0) :
  bv_extract 0 1 (bv_shiftr (bv_and value (BV 64 18446744073709551614)) (BV 64 1)) = BV 1 0.
Proof.
  Fail solve [previous_finish_lia].
  ZesuSsz.Automation2.IntegerReturn.zesu_return_target_bit_close.
Qed.

(* The alignment of the encoded integer, with its range; through the finisher. *)
Lemma target_bit_integer (R : Z) (Hlower : 0 <= R) (Hupper : R < 2 ^ 64)
    (Haligned : R mod 4 = 0) :
  bv_extract 0 1 (bv_shiftr (bv_and (Z_to_bv 64 R) (BV 64 18446744073709551614))
    (BV 64 1)) = BV 1 0.
Proof.
  Fail solve [previous_finish_lia].
  ZesuSsz.Automation2.BoundedArithmetic.zesu_finish_lia.
Qed.

(* A requested fact that mentions the bit, as a successor entry states it. *)
Lemma target_bit_decided (value : bv 64) (Haligned : bv_unsigned value mod 4 = 0) :
  bv_unsigned (bv_extract 0 1 (bv_shiftr
    (bv_and value (BV 64 18446744073709551614)) (BV 64 1))) <> 1.
Proof.
  Fail solve [previous_finish_lia].
  ZesuSsz.Automation2.IntegerReturn.zesu_return_target_bit_close.
Qed.

(* No alignment fact: refused. *)
Lemma target_bit_unaligned (value : bv 64) : True.
Proof.
  Fail assert (Hbit : bv_extract 0 1 (bv_shiftr
    (bv_and value (BV 64 18446744073709551614)) (BV 64 1)) = BV 1 0)
    by ZesuSsz.Automation2.IntegerReturn.zesu_return_target_bit_close.
  exact I.
Qed.

Print Assumptions target_bit_word.
Print Assumptions target_bit_integer.

(* A fact read from the folded precondition in a local proof; the context
   keeps the folded hypothesis. *)
Lemma folded_fact_range (R : Z) (Hdomain : target_domain R) : 0 <= R < 2 ^ 64.
Proof.
  Fail solve [zesu_lia].
  ZesuSsz.Automation2.IntegerReturn.zesu_return_folded_fact.
Qed.

Lemma folded_fact_alignment (R : Z) (Hdomain : target_domain R) : R mod 4 = 0.
Proof.
  Fail solve [zesu_lia].
  assert (Haligned : R mod 4 = 0) by ZesuSsz.Automation2.IntegerReturn.zesu_return_folded_fact.
  match goal with H : target_domain R |- _ => idtac end.
  exact Haligned.
Qed.

Lemma folded_fact_absent (R : Z) (Hrange : target_range R) : True.
Proof.
  Fail assert (Haligned : R mod 4 = 0) by ZesuSsz.Automation2.IntegerReturn.zesu_return_folded_fact.
  assert (Hlower : 0 <= R) by ZesuSsz.Automation2.IntegerReturn.zesu_return_folded_fact.
  exact I.
Qed.

(* The integer range read through the folded branch. *)
Lemma folded_integer_range (R : Z) (Hdomain : target_domain_constants R) : R mod 2 = 0.
Proof.
  tryif (match goal with H : R mod 4 = 0 |- _ => idtac end) then fail else idtac.
  ZesuSsz.Automation2.IntegerReturn.zesu_return_integer_range R
    ltac:(fun Hlower Hupper Haligned => clear -Haligned; zesu_lia).
Qed.

(* The alignment-fault branch, with the facts only in the folded
   precondition. *)
Lemma folded_integer_fault (R : Z) (Hdomain : target_domain_constants R) :
  SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False.
Proof. ZesuSsz.Automation2.IntegerReturn.zesu_return_integer_fault. Qed.

(* The return target's normalization, alignment only in the folded
   precondition. *)
Lemma folded_integer_normalize (Sigma : gFunctors) (R : Z)
    (Hdomain : target_domain_constants R) :
  LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))).
Proof. ZesuSsz.Automation2.IntegerReturn.zesu_return_integer_normalize. Qed.

Lemma folded_integer_normalize_unaligned (Sigma : gFunctors) (R : Z)
    (Hrange : target_range R) : True.
Proof.
  Fail assert (Hbad : LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))))
    by ZesuSsz.Automation2.IntegerReturn.zesu_return_integer_normalize.
  exact I.
Qed.

Print Assumptions folded_integer_fault.
Print Assumptions folded_integer_normalize.

(* Without the folded-fact reader, the same goals fail. *)
#[local] Ltac ZesuSsz.Automation2.IntegerReturn.zesu_return_folded_fact ::=
  fail "folded fact reader disabled".

Lemma folded_integer_needs_reader (Sigma : gFunctors) (R : Z)
    (Hdomain : target_domain_constants R) : True.
Proof.
  Fail assert (Heven : R mod 2 = 0) by
    ZesuSsz.Automation2.IntegerReturn.zesu_return_integer_range R
      ltac:(fun Hlower Hupper Haligned => clear -Haligned; zesu_lia).
  Fail assert (Hfault : SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False)
    by ZesuSsz.Automation2.IntegerReturn.zesu_return_integer_fault.
  Fail assert (Hbad : LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add (Z_to_bv 64 R) (BV 64 0))
      (BV 64 0xfffffffffffffffe)) (BV 64 0)))))
    by ZesuSsz.Automation2.IntegerReturn.zesu_return_integer_normalize.
  exact I.
Qed.
