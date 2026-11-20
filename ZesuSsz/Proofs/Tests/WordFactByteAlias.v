From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* decodeParentHeader 0568/059c (edges into join 0270): the successor asks
   the branch fact on a 16-bit word as `bv_unsigned (bv_concat 16 (nth 9 l)
   (nth 8 l)) = 0`, its positions typed at the contract's byte type (another
   name of `bv 8`), while the block holds it as the load it branched on,
   `bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take 2 (drop
   (Z.to_nat e) l)))) = 0` with a frame offset e. BytePositionEquations.
   zesu_word_fact_goal restates the goal's positions at `bv 8`, rewrites the
   window into byte positions, and takes the fact's bv_unsigned view. *)
Definition test_byte : Type := bv 8.

Lemma test_word_fact_byte_alias (sp : bv 64) (l : list test_byte) :
  2684354560 <= bv_unsigned sp < 3221225472 ->
  length l = 16%nat ->
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (@take (bv 8) (N.to_nat 2)
    (@drop (bv 8) (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551440) -
                             (bv_unsigned sp - 400 + 48 + 56 + 40 + 16 + 56))) l)))) = BV 64 0 ->
  bv_unsigned (bv_concat 16 (@nth test_byte 9 l (BV 8 0)) (@nth test_byte 8 l (BV 8 0))) = 0.
Proof.
  intros Hsp Hlen Hfact.
  ZesuSsz.Automation2.BytePositionEquations.zesu_word_fact_goal.
Qed.

(* The fact on two other bytes does not state the goal: refused. *)
Lemma test_word_fact_byte_alias_other (sp : bv 64) (l : list test_byte) :
  2684354560 <= bv_unsigned sp < 3221225472 ->
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (@take (bv 8) (N.to_nat 2)
    (@drop (bv 8) (Z.to_nat (bv_unsigned (sp + BV 64 10) - bv_unsigned sp)) l)))) = BV 64 0 ->
  bv_unsigned (bv_concat 16 (@nth test_byte 9 l (BV 8 0)) (@nth test_byte 8 l (BV 8 0))) = 0 ->
  bv_unsigned (bv_concat 16 (@nth test_byte 9 l (BV 8 0)) (@nth test_byte 8 l (BV 8 0))) = 0.
Proof.
  intros Hsp Hfact Hgoal. revert Hgoal.
  assert_fails (intros _; ZesuSsz.Automation2.BytePositionEquations.zesu_word_fact_goal).
  intros Hgoal. exact Hgoal.
Qed.
