From Coq Require Import Lists.List ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Open Scope Z_scope.

Lemma zesu_loop_bounded_endpoint64 (base length : Z) (count : bv 64) :
  0 <= base -> 0 <= length -> base + length < bv_modulus 64 ->
  bv_unsigned count < length ->
  bv_unsigned (bv_add (Z_to_bv 64 base) (bv_add count (BV 64 1))) =
    base + bv_unsigned count + 1.
Proof.
  intros Hbase Hlength Hextent Hcount.
  pose proof (bv_unsigned_in_range 64 count) as HcountRange.
  assert (HbaseRange : 0 <= base < bv_modulus 64) by lia.
  assert (Hstep : bv_unsigned (bv_add count (BV 64 1)) = bv_unsigned count + 1).
  { rewrite bv_unsigned_add_no_wrap_64;
      [rewrite bv_unsigned_BV; reflexivity | rewrite bv_unsigned_BV; unfold bv_modulus in *; lia]. }
  rewrite bv_unsigned_add_no_wrap_64;
    [rewrite (Z_to_bv_small 64 base HbaseRange), Hstep; lia |
     rewrite (Z_to_bv_small 64 base HbaseRange), Hstep; unfold bv_modulus in *; lia].
Qed.
