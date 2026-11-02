From Coq Require Import ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Require Import ZesuSsz.Automation.BitvectorFacts.
Open Scope Z_scope.

Lemma zesu_loop_zero_read_refutation (cursor input_end : bv 64) :
  bv_unsigned cursor < bv_unsigned input_end ->
  ~ (bv_signed (bv_add (bv_zero_extend 128 cursor) (BV 128 1)) <=
      bv_signed (bv_zero_extend 128 input_end)) -> False.
Proof.
  intros Hcursor Houtside. apply Houtside.
  rewrite (zesu_signed_zero_extend_add_64_128 cursor (BV 128 1))
    by (change (1 < 2 ^ 64); lia).
  rewrite zesu_signed_zero_extend_64_128, bv_unsigned_BV. lia.
Qed.

Lemma zesu_loop_zero_read_chain (cursor input_end : bv 64)
    (limit base length : Z) :
  bv_unsigned cursor < limit -> limit <= base + length ->
  base + length <= bv_unsigned input_end ->
  negb (bool_decide (bv_signed (bv_add (bv_zero_extend 128 cursor) (BV 128 1)) <=
                    bv_signed (bv_zero_extend 128 input_end))) = true -> False.
Proof.
  intros Hcursor Hlimit Hend Houtside.
  apply Bool.negb_true_iff in Houtside.
  apply bool_decide_eq_false_1 in Houtside.
  apply (zesu_loop_zero_read_refutation cursor input_end); [lia | exact Houtside].
Qed.

Lemma zesu_loop_zero_read_source_end (cursor : bv 64) (limit base length input_end : Z) :
  0 <= input_end < bv_modulus 64 ->
  bv_unsigned cursor < limit -> limit <= base + length -> base + length <= input_end ->
  negb (bool_decide (bv_signed (bv_add (bv_zero_extend 128 cursor) (BV 128 1)) <=
                    bv_signed (bv_zero_extend 128 (Z_to_bv 64 input_end)))) = true -> False.
Proof.
  intros Hrange Hcursor Hlimit Hend Houtside.
  eapply (zesu_loop_zero_read_chain cursor (Z_to_bv 64 input_end) limit base length);
    [exact Hcursor | exact Hlimit | rewrite (Z_to_bv_small 64 input_end Hrange); exact Hend | exact Houtside].
Qed.
