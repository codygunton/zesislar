From Coq Require Import ZArith.ZArith Lists.List.
Import ListNotations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The membership classifier of isla's semantic memory lookup
   (BvLinear.zesu_mem_range_class) and its gate (UninitRegions). Each helper
   succeeds only on the named verdict. *)
Ltac outside := ZesuSsz.Automation2.BvLinear.zesu_mem_range_class ltac:(idtac) ltac:(fail) ltac:(fail).
Ltac possible := ZesuSsz.Automation2.BvLinear.zesu_mem_range_class ltac:(fail) ltac:(idtac) ltac:(fail).
Ltac unread := ZesuSsz.Automation2.BvLinear.zesu_mem_range_class ltac:(fail) ltac:(fail) ltac:(idtac).

(* Same root: the constant offsets decide. *)
Lemma mem_range_same_root (p : bv 64) : True.
Proof.
  assert_succeeds (assert (bv_unsigned p + 8 <= bv_unsigned p + 16 < bv_unsigned p + 8 + 4 \/
                           bv_unsigned p + 8 = bv_unsigned p + 16) as H; [outside; shelve | ]).
  assert_succeeds (assert (bv_unsigned p + 8 <= bv_unsigned p < bv_unsigned p + 8 + 4 \/
                           bv_unsigned p + 8 = bv_unsigned p) as H; [outside; shelve | ]).
  assert_succeeds (assert (bv_unsigned p <= bv_unsigned p + 4 < bv_unsigned p + 8 \/
                           bv_unsigned p = bv_unsigned p + 4) as H; [possible; shelve | ]).
  exact I.
Qed.

(* A stack slot through a local definition: the address wraps modulo 2^64.
   sp - 312 is outside the 112 bytes at sp - 512 and the 216 bytes at
   sp - 596, may lie in the 216 bytes at sp - 336, and a region of unknown
   length at sp - 336 is not read. A two-byte array has length 2. *)
Lemma mem_range_stack_slots (sp : bv 64) : True.
Proof.
  pose (LET0 := (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551304)%bv).
  assert_succeeds (assert (bv_unsigned sp - 400 - 112 <= bv_unsigned LET0 <
                             bv_unsigned sp - 400 - 112 + 112 \/
                           bv_unsigned sp - 400 - 112 = bv_unsigned LET0) as H; [outside; shelve | ]).
  assert_succeeds (assert (bv_unsigned sp - 596 <= bv_unsigned LET0 < bv_unsigned sp - 596 + 216 \/
                           bv_unsigned sp - 596 = bv_unsigned LET0) as H; [outside; shelve | ]).
  assert_succeeds (assert (bv_unsigned sp - 336 <= bv_unsigned LET0 < bv_unsigned sp - 336 + 216 \/
                           bv_unsigned sp - 336 = bv_unsigned LET0) as H; [possible; shelve | ]).
  assert_succeeds (assert (forall bytes : list (bv 8),
                bv_unsigned sp - 336 <= bv_unsigned LET0 < bv_unsigned sp - 336 + Z.of_nat (length bytes) \/
                bv_unsigned sp - 336 = bv_unsigned LET0) as H; [intros bytes; unread; shelve | ]).
  assert_succeeds (assert (bv_unsigned sp - 80 <= bv_unsigned LET0 <
                             bv_unsigned sp - 80 + Z.of_nat (length [BV 8 0; BV 8 1]) * Z.of_N (8 `div` 8) \/
                           bv_unsigned sp - 80 = bv_unsigned LET0) as H; [outside; shelve | ]).
  exact I.
Qed.

(* Constants decide by arithmetic; a closed term that is not a numeral is not read. *)
Lemma mem_range_constants : True.
Proof.
  assert_succeeds (assert (2688552704 <= 2688552800 < 2688552704 + 8 \/ 2688552704 = 2688552800) as H;
    [outside; shelve | ]).
  assert_succeeds (assert (2688552704 <= 2688552708 < 2688552704 + 8 \/ 2688552704 = 2688552708) as H;
    [possible; shelve | ]).
  assert_succeeds (assert (2688552704 <= Z.of_nat 5 < 2688552704 + 8 \/ 2688552704 = Z.of_nat 5) as H;
    [unread; shelve | ]).
  exact I.
Qed.

(* Different roots are not read, whatever the hypotheses say. *)
Lemma mem_range_different_roots (p q : bv 64) (Hq : bv_unsigned q = bv_unsigned p + 4) : True.
Proof.
  assert_succeeds (assert (bv_unsigned p <= bv_unsigned q < bv_unsigned p + 8 \/
                           bv_unsigned p = bv_unsigned q) as H; [unread; shelve | ]).
  assert_succeeds (assert (2688552704 <= bv_unsigned q < 2688552704 + 8 \/
                           2688552704 = bv_unsigned q) as H; [unread; shelve | ]).
  exact I.
Qed.

(* The lookup end to end: a region that holds the address is found; a region
   that does not is refused by the gate and by isla's hint after it. *)
Section lookup.
  Context `{!islaG Sigma}.

  Lemma mem_lookup_found (p : bv 64) :
    exists G, FindHypEqual (FICMemMapstoSemantic (bv_unsigned p + 4)) (bv_unsigned p ↦ₘ? 8)
      (mem_mapsto_kind_prop (bv_unsigned p) (MKUninit (bv_unsigned p) 8)) G.
  Proof. eexists. typeclasses eauto. Qed.

  Lemma mem_lookup_refused (p : bv 64) : True.
  Proof.
    Fail (assert (exists G, FindHypEqual (FICMemMapstoSemantic (bv_unsigned p + 12)) (bv_unsigned p ↦ₘ? 8)
      (mem_mapsto_kind_prop (bv_unsigned p) (MKUninit (bv_unsigned p) 8)) G)
      by (eexists; typeclasses eauto)).
    exact I.
  Qed.
End lookup.
