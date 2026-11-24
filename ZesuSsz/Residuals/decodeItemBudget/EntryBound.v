(* The loop-entry bound of the charged rlp.decodeItem (plan Stage T, T7),
   hand-written by the region owner from the statement the package route
   leaves at the loop entries +0xb4 and +0x154 (zesu_memory_frame_budget):
   the potential of the loop head, 5 * (end - cursor) + 12, is at most the
   entry bound 52 because the code enters a length-of-length loop only with
   a first byte in [184, 191] (string) or [248, 255] (list), i.e. a
   length-of-length in [1, 8] that is also below the input length. *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Local Open Scope Z_scope.

Lemma decodeItemBudgetMask (c : Z) (b : bv 8) :
  0 <= c < 256 -> 256 - c <= bv_unsigned b ->
  bv_unsigned (bv_and (bv_add (bv_and (bv_sign_extend 64 b) (BV 64 255)) (Z_to_bv 64 c)) (BV 64 255)) =
  bv_unsigned b + c - 256.
Proof.
  intros Hc Hb. pose proof (bv_unsigned_in_range _ b) as Hr. unfold bv_modulus in Hr. simpl in Hr.
  rewrite !bv_and_unsigned bv_add_unsigned bv_and_unsigned bv_sign_extend_unsigned Z_to_bv_unsigned.
  change (bv_unsigned (BV 64 255)) with (Z.ones 8).
  rewrite !Z.land_ones; try lia.
  unfold bv_wrap, bv_modulus. simpl (Z.of_N 64).
  assert (Hs : bv_signed b mod 2^64 mod 2^8 = bv_unsigned b).
  { rewrite -Znumtheory.Zmod_div_mod; [| lia | lia | exists (2^56); reflexivity].
    unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. simpl (Z.of_N 8).
    change (2 ^ 8 `div` 2) with 128. change (2 ^ 8) with 256 in *.
    rewrite Zminus_mod_idemp_l. replace (bv_unsigned b + 128 - 128) with (bv_unsigned b) by lia.
    apply Z.mod_small. lia. }
  rewrite Hs. rewrite (Z.mod_small c); [|lia].
  rewrite (Z.mod_small (bv_unsigned b + c)); [|lia].
  rewrite -(Z.mod_add _ (-1)); [|lia]. rewrite Z.mod_small; lia.
Qed.

Lemma decodeItemBudgetEntryBound (args : DecodeItemArgs) (returnAddress c : Z) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  0 <= c < 256 ->
  256 - c <= bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) + c - 256 <= 8 ->
  bv_unsigned (nth 0 (decodeItemInputBytes args) (BV 8 0)) + c - 256 <
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) ->
  0 <= 5 * (bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args))
       (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))
          (Z_to_bv 64 c)) (BV 64 255)) (BV 64 1))) -
     bv_unsigned (bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (BV 64 1))) + 12 <= 52.
Proof.
  intros Hdomain Hc Hlow Hhigh Hlen.
  set (b := nth 0 (decodeItemInputBytes args) (BV 8 0)) in *.
  assert (Hw : 0 <= decodeItemInputPointer args /\ 0 <= decodeItemInputLength args /\
               decodeItemInputPointer args + decodeItemInputLength args < 2^64).
  { destruct Hdomain as [_ Hw]. unfold decodeItemC1BDomain, decodeItemArgsWellFormed, decodeItemEntryLayout in Hw.
    unfold word64Modulus in *. lia. }
  pose proof (decodeItemBudgetMask c b Hc Hlow) as Hm.
  set (M := bv_and _ (BV 64 255)) in *.
  rewrite Z_to_bv_unsigned in Hlen. unfold bv_wrap, bv_modulus in Hlen. simpl (Z.of_N 64) in Hlen.
  rewrite Z.mod_small in Hlen; [|lia].
  rewrite !bv_add_unsigned Z_to_bv_unsigned Hm. change (bv_unsigned (BV 64 1)) with 1.
  unfold bv_wrap, bv_modulus. simpl (Z.of_N 64).
  rewrite (Z.mod_small (decodeItemInputPointer args)); [|lia].
  rewrite (Z.mod_small (bv_unsigned b + c - 256 + 1)); [|lia].
  rewrite (Z.mod_small (_ + (_ + 1))); [|lia].
  rewrite (Z.mod_small (_ + 1)); [|lia].
  lia.
Qed.
