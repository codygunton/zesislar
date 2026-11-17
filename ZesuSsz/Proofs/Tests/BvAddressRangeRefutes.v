From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The address lies 8 bytes past a 4-byte region: the normal form refutes the
   membership side condition, and bv_solve fails at once. *)
Lemma address_range_past_end (p : bv 64) : True.
Proof.
  assert_succeeds (assert (bv_unsigned p + 8 <= bv_unsigned p + 16 < bv_unsigned p + 8 + 4 \/
                           bv_unsigned p + 8 = bv_unsigned p + 16) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_bv_address_range_refutes; shelve | ]).
  Fail (assert (bv_unsigned p + 8 <= bv_unsigned p + 16 < bv_unsigned p + 8 + 4 \/
                bv_unsigned p + 8 = bv_unsigned p + 16) by bv_solve).
  exact I.
Qed.

(* An address below the region start is refuted for any region size. *)
Lemma address_range_below_start (p : bv 64) (n : Z) : True.
Proof.
  assert_succeeds (assert (bv_unsigned p + 8 <= bv_unsigned p < bv_unsigned p + 8 + n \/
                           bv_unsigned p + 8 = bv_unsigned p) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_bv_address_range_refutes; shelve | ]).
  exact I.
Qed.

(* Stack slots through local definitions: sp - 8 is outside the 112 bytes at
   sp - 512 modulo 2^64, and inside the 400 bytes at sp - 400. *)
Lemma address_range_stack_slots (sp : bv 64) : True.
Proof.
  pose (LET0 := (sp + BV 64 18446744073709551216)%bv).
  pose (LET2 := (LET0 + BV 64 392)%bv).
  assert_succeeds (assert (bv_unsigned sp - 400 - 112 <= bv_unsigned LET2 <
                             bv_unsigned sp - 400 - 112 + 112 \/
                           bv_unsigned sp - 400 - 112 = bv_unsigned LET2) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_bv_address_range_refutes; shelve | ]).
  Fail (assert (bv_unsigned sp - 400 <= bv_unsigned LET2 < bv_unsigned sp - 400 + 400 \/
                bv_unsigned sp - 400 = bv_unsigned LET2) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_bv_address_range_refutes | ]).
  exact I.
Qed.

(* An address inside the region is not refuted, and bv_solve proves it. *)
Lemma address_range_inside (p : bv 64) :
  bv_unsigned p <= bv_unsigned p + 4 < bv_unsigned p + 8 \/ bv_unsigned p = bv_unsigned p + 4.
Proof.
  Fail ZesuSsz.Automation2.BvLinear.zesu_bv_address_range_refutes.
  bv_solve.
Qed.

(* Different bases, or a symbolic size past a positive offset, are left to the
   solver: here the facts prove membership. *)
Lemma address_range_other_base (p q : bv 64) (n : Z)
    (Hq : bv_unsigned q = bv_unsigned p + 4) (Hn : 8 <= n) :
  bv_unsigned p <= bv_unsigned q < bv_unsigned p + n \/ bv_unsigned p = bv_unsigned q.
Proof.
  Fail ZesuSsz.Automation2.BvLinear.zesu_bv_address_range_refutes.
  bv_solve.
Qed.
