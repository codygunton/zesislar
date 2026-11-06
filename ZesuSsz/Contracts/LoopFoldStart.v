From Coq Require Import Lists.List ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Contracts.ByteWindowFoldIndex.
Require Import ZesuSsz.Contracts.LoopSourceBounds.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Open Scope Z_scope.

Lemma loop_fold_start_from_complete_source_domain (args : DecodeItemArgs) (returnAddress : Z)
    (cursor endpoint count acc : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  cursor = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1) ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add count (BV 64 1)) ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 count) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))))) = true ->
  1 <= bv_unsigned count -> acc = BV 64 0 ->
  let index := bv_unsigned cursor - (decodeItemInputPointer args + 1) in
  index = 0 /\ 0 <= index /\
  bv_unsigned cursor = decodeItemInputPointer args + 1 + index /\
  bv_unsigned cursor < bv_unsigned endpoint /\
  bv_unsigned acc = zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat index).
Proof.
  intros Hdomain Hcursor Hendpoint HcountGuard Hpositive Hacc.
  unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
    decodeItemEntryLayout in Hdomain.
  repeat match goal with Hpart : _ /\ _ |- _ => destruct Hpart end.
  apply Bool.negb_true_iff in HcountGuard. apply bool_decide_eq_false_1 in HcountGuard.
  rewrite !zesu_signed_zero_extend_64_128 in HcountGuard.
  assert (HlengthRange : 0 <= decodeItemInputLength args < bv_modulus 64)
    by (unfold bv_modulus in *; lia).
  rewrite (Z_to_bv_small 64 (decodeItemInputLength args) HlengthRange) in HcountGuard.
  assert (Hcount : bv_unsigned count < decodeItemInputLength args) by lia.
  assert (Hbase : 0 <= decodeItemInputPointer args) by assumption.
  assert (Hlength : 0 <= decodeItemInputLength args) by assumption.
  assert (Hextent : decodeItemInputPointer args + decodeItemInputLength args < bv_modulus 64)
    by (unfold bv_modulus in *; assumption).
  assert (HbaseRange : 0 <= decodeItemInputPointer args < bv_modulus 64) by lia.
  assert (Hstart : bv_unsigned cursor = decodeItemInputPointer args + 1).
  { rewrite Hcursor. rewrite bv_unsigned_add_no_wrap_64;
      [rewrite (Z_to_bv_small 64 (decodeItemInputPointer args) HbaseRange);
       rewrite bv_unsigned_BV; lia |
       rewrite (Z_to_bv_small 64 (decodeItemInputPointer args) HbaseRange);
       rewrite bv_unsigned_BV; unfold bv_modulus in *; lia]. }
  assert (Hlimit : bv_unsigned endpoint = decodeItemInputPointer args + bv_unsigned count + 1).
  { rewrite Hendpoint. apply (zesu_loop_bounded_endpoint64
      (decodeItemInputPointer args) (decodeItemInputLength args) count); assumption. }
  cbn zeta. rewrite Hstart, Hlimit, Hacc.
  replace (decodeItemInputPointer args + 1 - (decodeItemInputPointer args + 1)) with 0 by lia.
  repeat split; try lia.
Qed.

From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics.

Lemma zesu_loop_first_pass_intro {Sigma} {A B C D E : Type}
    (resources : A -> B -> C -> D -> E -> iProp Sigma)
    (invariants : A -> B -> C -> D -> E -> Prop)
    (initial : Prop) (a : A) (b : B) (c : C) (d : D) (e : E)
    (derive : initial -> invariants a b c d e) :
  resources a b c d e ∗ ⌜initial⌝ ⊢
  ∃ a' b' c' d' e', resources a' b' c' d' e' ∗ ⌜invariants a' b' c' d' e'⌝.
Proof.
  iIntros "[Hresources %Hinitial]".
  iExists a, b, c, d, e. iFrame.
  iPureIntro. exact (derive Hinitial).
Qed.
