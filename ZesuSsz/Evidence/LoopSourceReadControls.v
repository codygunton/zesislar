Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.LoopSourceBounds.
Require Import ZesuSsz.Automation.LoopCursorRanges.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
From Coq Require Import Lists.List ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Open Scope Z_scope.

Lemma loop_read_from_complete_source_domain (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint length_word count : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  length_word = Z_to_bv 64 (decodeItemInputLength args) ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add count (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 count) >=
                    bv_signed (bv_zero_extend 128 length_word))) = true ->
  (0 <= bv_unsigned cursor - decodeItemInputPointer args <
       Z.of_nat (List.length (decodeItemInputBytes args))) /\
  nth_error (decodeItemInputBytes args) (Z.to_nat (bv_unsigned cursor - decodeItemInputPointer args)) =
    Some (nth (Z.to_nat (bv_unsigned cursor - decodeItemInputPointer args))
              (decodeItemInputBytes args) (BV 8 0)).
Proof.
  intros Hdomain HlengthWord Hendpoint Hindex HcursorOrigin Hcursor HcountGuard.
  unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
    decodeItemEntryLayout in Hdomain.
  repeat match goal with Hsource : _ /\ _ |- _ => destruct Hsource end.
  apply Bool.negb_true_iff in HcountGuard. apply bool_decide_eq_false_1 in HcountGuard.
  rewrite !zesu_signed_zero_extend_64_128 in HcountGuard.
  assert (HlengthRange : 0 <= decodeItemInputLength args < bv_modulus 64)
    by (unfold bv_modulus, word64Modulus in *; lia).
  rewrite HlengthWord in HcountGuard.
  rewrite (Z_to_bv_small 64 (decodeItemInputLength args) HlengthRange) in HcountGuard.
  assert (Hcount : bv_unsigned count < decodeItemInputLength args) by lia.
  assert (Hbase : 0 <= decodeItemInputPointer args) by assumption.
  assert (Hlength : 0 <= decodeItemInputLength args) by assumption.
  assert (Hextent : decodeItemInputPointer args + decodeItemInputLength args < bv_modulus 64)
    by (unfold bv_modulus, word64Modulus in *; assumption).
  rewrite Hendpoint in Hcursor.
  rewrite (zesu_loop_bounded_endpoint64 (decodeItemInputPointer args)
    (decodeItemInputLength args) count Hbase Hlength Hextent Hcount) in Hcursor.
  assert (Hread : 0 <= bv_unsigned cursor - decodeItemInputPointer args < decodeItemInputLength args).
  { eapply (zesu_loop_read_range (decodeItemInputPointer args) (decodeItemInputPointer args + 1)
      (bv_unsigned cursor) (decodeItemInputPointer args + bv_unsigned count + 1)
      (decodeItemInputLength args)); [lia | lia | exact Hcursor | lia]. }
  match goal with HsourceLength : decodeItemInputLength args =
    Z.of_nat (List.length (decodeItemInputBytes args)) |- _ => rewrite HsourceLength in Hread end.
  split; [exact Hread | apply zesu_loop_read_lookup; exact Hread].
Qed.

Lemma loop_owned_read_from_complete_source_domain (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint length_word count : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  length_word = Z_to_bv 64 (decodeItemInputLength args) ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add count (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 count) >=
                    bv_signed (bv_zero_extend 128 length_word))) = true ->
  (0 <= bv_unsigned cursor - bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)) <
       Z.of_nat (List.length (decodeItemInputBytes args))) /\
  nth_error (decodeItemInputBytes args)
    (Z.to_nat (bv_unsigned cursor - bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)))) =
    Some (nth (Z.to_nat (bv_unsigned cursor - bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args))))
              (decodeItemInputBytes args) (BV 8 0)).
Proof.
  intros Hdomain HlengthWord Hendpoint Hindex HcursorOrigin Hcursor HcountGuard.
  pose proof (loop_read_from_complete_source_domain args returnAddress index cursor endpoint
    length_word count Hdomain HlengthWord Hendpoint Hindex HcursorOrigin Hcursor HcountGuard) as Hread.
  assert (HbaseView : bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)) = decodeItemInputPointer args).
  { unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
      decodeItemEntryLayout in Hdomain.
    repeat match goal with Hsource : _ /\ _ |- _ => destruct Hsource end.
    apply Z_to_bv_small. unfold bv_modulus, word64Modulus in *. lia. }
  rewrite HbaseView. exact Hread.
Qed.
