From Coq Require Import ZArith.ZArith Lists.List.
Import ListNotations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The memory lookup membership pre-check (BvLinear.zesu_mem_range_refutes),
   through the hooked library bv_solve (the qualified name; the bare name is
   the project's tactic notation). Same root: the constant offsets decide; an
   address 8 bytes past a 4-byte region, or below the region start, is refused
   and bv_solve fails at once. *)
Lemma mem_range_same_root (p : bv 64) : True.
Proof.
  assert_succeeds (assert (bv_unsigned p + 8 <= bv_unsigned p + 16 < bv_unsigned p + 8 + 4 \/
                           bv_unsigned p + 8 = bv_unsigned p + 16) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes; shelve | ]).
  assert_succeeds (assert (bv_unsigned p + 8 <= bv_unsigned p < bv_unsigned p + 8 + 4 \/
                           bv_unsigned p + 8 = bv_unsigned p) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes; shelve | ]).
  Fail (assert (bv_unsigned p + 8 <= bv_unsigned p + 16 < bv_unsigned p + 8 + 4 \/
                bv_unsigned p + 8 = bv_unsigned p + 16) by stdpp.bitvector.tactics.bv_solve).
  exact I.
Qed.

(* An address inside the region is kept, and bv_solve proves it. *)
Lemma mem_range_inside (p : bv 64) :
  bv_unsigned p <= bv_unsigned p + 4 < bv_unsigned p + 8 \/ bv_unsigned p = bv_unsigned p + 4.
Proof.
  Fail ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes.
  stdpp.bitvector.tactics.bv_solve.
Qed.

(* A stack slot through a local definition: the address wraps modulo 2^64,
   sp - 312 is outside the 112 bytes at sp - 512 and outside the 216 bytes at
   sp - 596, but not outside the 216 bytes at sp - 336, nor a region of
   unknown length at sp - 336. A two-byte array has length 2. *)
Lemma mem_range_stack_slots (sp : bv 64) : True.
Proof.
  pose (LET0 := (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551304)%bv).
  assert_succeeds (assert (bv_unsigned sp - 400 - 112 <= bv_unsigned LET0 <
                             bv_unsigned sp - 400 - 112 + 112 \/
                           bv_unsigned sp - 400 - 112 = bv_unsigned LET0) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes; shelve | ]).
  assert_succeeds (assert (bv_unsigned sp - 596 <= bv_unsigned LET0 < bv_unsigned sp - 596 + 216 \/
                           bv_unsigned sp - 596 = bv_unsigned LET0) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes; shelve | ]).
  Fail (assert (bv_unsigned sp - 336 <= bv_unsigned LET0 < bv_unsigned sp - 336 + 216 \/
                bv_unsigned sp - 336 = bv_unsigned LET0) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes | ]).
  Fail (assert (forall bytes : list (bv 8),
                bv_unsigned sp - 336 <= bv_unsigned LET0 < bv_unsigned sp - 336 + Z.of_nat (length bytes) \/
                bv_unsigned sp - 336 = bv_unsigned LET0) as H;
    [intros bytes; ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes | ]).
  assert_succeeds (assert (bv_unsigned sp - 80 <= bv_unsigned LET0 <
                             bv_unsigned sp - 80 + Z.of_nat (length [BV 8 0; BV 8 1]) * Z.of_N (8 `div` 8) \/
                           bv_unsigned sp - 80 = bv_unsigned LET0) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes; shelve | ]).
  exact I.
Qed.

(* Constants decide by arithmetic. *)
Lemma mem_range_constants : True.
Proof.
  assert_succeeds (assert (2688552704 <= 2688552800 < 2688552704 + 8 \/ 2688552704 = 2688552800) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes; shelve | ]).
  Fail (assert (2688552704 <= 2688552708 < 2688552704 + 8 \/ 2688552704 = 2688552708) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes | ]).
  exact I.
Qed.

(* Different roots with no hypothesis on both (or, for a constant region, none
   on the address) are refused. *)
Lemma mem_range_unlinked (p q : bv 64) : True.
Proof.
  assert_succeeds (assert (bv_unsigned p <= bv_unsigned q < bv_unsigned p + 8 \/
                           bv_unsigned p = bv_unsigned q) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes; shelve | ]).
  assert_succeeds (assert (2688552704 <= bv_unsigned q < 2688552704 + 8 \/
                           2688552704 = bv_unsigned q) as H;
    [ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes; shelve | ]).
  exact I.
Qed.

(* A fact that links the roots keeps the goal for the solver, which proves it. *)
Lemma mem_range_linked (p q : bv 64) (Hq : bv_unsigned q = bv_unsigned p + 4) :
  bv_unsigned p <= bv_unsigned q < bv_unsigned p + 8 \/ bv_unsigned p = bv_unsigned q.
Proof.
  Fail ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes.
  stdpp.bitvector.tactics.bv_solve.
Qed.

(* A fact on the address keeps a constant region for the solver. *)
Lemma mem_range_constant_linked (q : bv 64) (Hq : bv_unsigned q = 2688552708) :
  2688552704 <= bv_unsigned q < 2688552704 + 8 \/ 2688552704 = bv_unsigned q.
Proof.
  Fail ZesuSsz.Automation2.BvLinear.zesu_mem_range_refutes.
  stdpp.bitvector.tactics.bv_solve.
Qed.
