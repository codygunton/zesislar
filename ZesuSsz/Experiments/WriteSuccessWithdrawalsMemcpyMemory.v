From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.

Import ListNotations.

Lemma writeSuccessMemcpyByteReadValue (byte : bv 8) :
  bv_to_bvn (Z_to_bv (8 * 1) (little_endian_to_bv 8 [byte])) =
    bv_to_bvn byte.
Proof.
  apply (proj2 (bvn_eq _ _)). split; first reflexivity.
  unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn.
  rewrite Z.shiftl_0_l. rewrite Z.lor_0_r.
  apply Z.mod_small. pose proof (bv_unsigned_in_range 8 byte) as Hrange.
  cbn in Hrange. exact Hrange.
Qed.

Lemma writeSuccessMemcpyReadByte memory source bytes index byte :
  read_mem_list memory source (N.of_nat (length bytes)) = Some bytes ->
  nth_error bytes index = Some byte ->
  read_mem memory (source + Z.of_nat index) 1 = Some (bv_to_bvn byte).
Proof.
  intros Hread Hnth.
  destruct (nth_error_split bytes index Hnth) as
    (prefix & suffix & Hbytes & Hprefix).
  subst bytes.
  rewrite length_app in Hread. cbn in Hread.
  destruct (read_mem_list_split memory source (length prefix)
    (S (length suffix)) (prefix ++ byte :: suffix) Hread) as
    (actualPrefix & actualRest & Hparts & HactualPrefix & HactualRest &
     HreadPrefix & HreadRest).
  have HprefixEq : actualPrefix = prefix.
  { have Hleft := f_equal (firstn (length prefix)) Hparts.
    rewrite !firstn_app in Hleft.
    rewrite HactualPrefix in Hleft. rewrite !Nat.sub_diag in Hleft.
    rewrite !firstn_all in Hleft. rewrite !firstn_O in Hleft.
    rewrite !app_nil_r in Hleft.
    rewrite <- HactualPrefix, firstn_all in Hleft. symmetry. exact Hleft. }
  subst actualPrefix.
  apply app_inv_head in Hparts. subst actualRest.
  destruct (read_mem_list_split memory
    (source + Z.of_nat (length prefix)) 1 (length suffix)
    (byte :: suffix) HreadRest) as
    (actualByte & actualSuffix & Hparts & HactualByte & HactualSuffix &
     HreadByte & HreadSuffix).
  destruct actualByte as [|head tail]; cbn in HactualByte; first lia.
  destruct tail; cbn in HactualByte; last lia.
  inversion Hparts. subst head actualSuffix.
  rewrite Hprefix in HreadByte.
  unfold read_mem. rewrite HreadByte. cbn.
  f_equal. apply writeSuccessMemcpyByteReadValue.
Qed.

Print Assumptions writeSuccessMemcpyByteReadValue.
Print Assumptions writeSuccessMemcpyReadByte.
