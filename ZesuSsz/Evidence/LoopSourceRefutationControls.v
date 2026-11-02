Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.LoopSourceBounds.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
From Coq Require Import ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Open Scope Z_scope.

Lemma loop_zero_from_complete_source_domain (args : DecodeItemArgs) (returnAddress : Z)
    (cursor endpoint length_word count : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  length_word = Z_to_bv 64 (decodeItemInputLength args) ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add count (BV 64 1)) ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 count) >=
                    bv_signed (bv_zero_extend 128 length_word))) = true ->
  negb (bool_decide (bv_signed (bv_add (bv_zero_extend 128 cursor) (BV 128 1)) <=
                    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputEnd args))))) = true -> False.
Proof.
  intros Hdomain HlengthWord Hendpoint Hcursor HcountGuard Houtside.
  unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
    decodeItemEntryLayout in Hdomain.
  repeat match goal with Hsource : _ /\ _ |- _ => destruct Hsource end.
  eapply (zesu_loop_source_zero_arm64 (decodeItemInputPointer args) (decodeItemInputLength args)
    (decodeItemInputEnd args) cursor endpoint length_word count); try eassumption;
    unfold bv_modulus, word64Modulus in *; lia.
Qed.
