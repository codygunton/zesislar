Require Import stdpp.bitvector.definitions.
Require Import stdpp.list_numbers.
From Coq Require Import List NArith ZArith Lia.
Set Default Proof Mode "Classic".

Definition byte_extracts281 {width : N} (count : nat) (word : bv width) :
    list (bv 8) :=
  (fun index : nat => bv_extract (8 * N.of_nat index)%N 8 word) <$> seq 0 count.

Lemma byte_extracts_codec281 (width : N) (count : nat) (word : bv width) :
  byte_extracts281 count word =
    bv_to_little_endian (Z.of_nat count) 8 (bv_unsigned word).
Proof.
  unfold byte_extracts281.
  apply (list_eq_same_length _ _ count).
  - rewrite length_bv_to_little_endian; [apply Nat2Z.id | lia].
  - rewrite length_fmap. rewrite length_seq. reflexivity.
  - intros index left right Hindex Hleft Hright.
    rewrite list_lookup_fmap in Hleft.
    rewrite lookup_seq_lt in Hleft; [|exact Hindex].
    cbn in Hleft. inversion Hleft; subst left.
    apply (bv_to_little_endian_lookup_Some (Z.of_nat count) 8
      (bv_unsigned word) index right) in Hright; [|lia].
    destruct Hright as [_ ->].
    apply bv_eq. rewrite bv_extract_unsigned. rewrite Z_to_bv_unsigned.
    rewrite N2Z.inj_mul. rewrite nat_N_Z. cbn.
    rewrite Z.mul_comm. reflexivity.
Qed.
