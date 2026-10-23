Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SailEval.
From Coq Require Import Bool List ZArith Lia.
Require Import SailStdpp.MachineWord SailStdpp.Values SailStdpp.Operators_mwords.
From stdpp Require Import bitvector.definitions.
Import ListNotations.
Open Scope Z_scope.

Lemma sail_byte_lor_shift (item : SailStdpp.Values.mword 8) value :
  Z.lor (bv_unsigned item) (Z.shiftl value 8) =
    Z.add (Z.mul value 256) (bv_unsigned item).
Proof.
  assert (Hland : Z.land (bv_unsigned item) (Z.shiftl value 8) = 0).
  { apply Z.bits_inj. intro index. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_ge_dec index 0) as [Hnegative|Hnonnegative].
    { rewrite Z.testbit_neg_r by lia. reflexivity. }
    destruct (Z_lt_ge_dec index 8) as [Hlow|Hhigh].
    { rewrite Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r value (index - 8)) by lia.
      apply andb_false_r. }
    assert (Hitem : 0 <= bv_unsigned item < 2 ^ 8).
    { exact (bv_unsigned_in_range _ item). }
    replace (bv_unsigned item) with (Z.modulo (bv_unsigned item) (2 ^ 8))
      at 1 by (apply Z.mod_small; exact Hitem).
    rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  pose proof (Z.add_lor_land (bv_unsigned item) (Z.shiftl value 8)) as Hsum.
  rewrite Hland in Hsum.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  change (2 ^ 8) with 256 in *.
  lia.
Qed.
Print Assumptions sail_byte_lor_shift.

Lemma sail_fold_uint_little_endian (input : list (SailStdpp.Values.mword 8)) :
  fold_left (fun accumulator (item : SailStdpp.Values.mword 8) =>
    Z.add (Z.mul accumulator 256) (@uint 8 item)) input 0 =
  little_endian_to_bv 8 (List.rev input).
Proof.
  induction input as [|input item IH] using rev_ind.
  - reflexivity.
  - rewrite fold_left_app. cbn [List.fold_left].
    rewrite sail_uint_unsigned, IH, rev_app_distr.
    cbn [List.rev List.app little_endian_to_bv fmap stdpp.list.list_fmap stdpp.list_numbers.little_endian_to_Z].
    rewrite sail_byte_lor_shift. reflexivity.
Qed.
Print Assumptions sail_fold_uint_little_endian.

Lemma sail_fold_uint_bound (input : list (SailStdpp.Values.mword 8)) :
  0 <= fold_left (fun accumulator (item : SailStdpp.Values.mword 8) =>
    Z.add (Z.mul accumulator 256) (@uint 8 item)) input 0 <
    2 ^ (Z.of_nat (length input) * 8).
Proof.
  rewrite sail_fold_uint_little_endian.
  pose proof (little_endian_to_bv_bound 8 (List.rev input)) as Hbound.
  rewrite rev_length in Hbound. exact Hbound.
Qed.
