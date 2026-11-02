From Coq Require Import ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.LoopReadRefutation.
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

Lemma zesu_loop_source_zero_arm64 (base length input_end : Z)
    (cursor endpoint length_word count : bv 64) :
  0 <= base -> 0 <= length -> base + length < bv_modulus 64 ->
  0 <= input_end < bv_modulus 64 -> base + length <= input_end ->
  length_word = Z_to_bv 64 length ->
  endpoint = bv_add (Z_to_bv 64 base) (bv_add count (BV 64 1)) ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 count) >=
                    bv_signed (bv_zero_extend 128 length_word))) = true ->
  negb (bool_decide (bv_signed (bv_add (bv_zero_extend 128 cursor) (BV 128 1)) <=
                    bv_signed (bv_zero_extend 128 (Z_to_bv 64 input_end)))) = true -> False.
Proof.
  intros Hbase Hlength Hextent HendRange HinputEnd HlengthWord Hendpoint Hcursor HcountGuard Houtside.
  apply Bool.negb_true_iff in HcountGuard. apply bool_decide_eq_false_1 in HcountGuard.
  rewrite !zesu_signed_zero_extend_64_128 in HcountGuard.
  assert (HlengthRange : 0 <= length < bv_modulus 64) by lia.
  rewrite HlengthWord, (Z_to_bv_small 64 length HlengthRange) in HcountGuard.
  assert (Hcount : bv_unsigned count < length) by lia.
  rewrite Hendpoint, (zesu_loop_bounded_endpoint64 base length count Hbase Hlength Hextent Hcount)
    in Hcursor.
  eapply (zesu_loop_zero_read_source_end cursor (base + bv_unsigned count + 1) base length input_end);
    [exact HendRange | exact Hcursor | lia | exact HinputEnd | exact Houtside].
Qed.
