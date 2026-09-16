Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.

Definition transactionChainWordImage (value tagWord : bv 64) : list (bv 8) :=
  bv_to_little_endian 8 8 (bv_unsigned value) ++
  bv_to_little_endian 8 8 (bv_unsigned tagWord).

Lemma transactions_chain_word_image value tagWord :
  transactionChainWordImage value tagWord !! 8%nat = Some (bv_extract 0 8 tagWord) /\
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (transactionChainWordImage value tagWord))) = value /\
  length (transactionChainWordImage value tagWord) = 16%nat.
Proof.
  have Hlength : length (bv_to_little_endian 8 8 (bv_unsigned value)) = 8%nat.
  { rewrite length_bv_to_little_endian; lia. }
  unfold transactionChainWordImage. split.
  - rewrite lookup_app_r; [rewrite Hlength Nat.sub_diag | rewrite Hlength; lia].
    apply bv_to_little_endian_lookup_Some; [lia |]. split; [lia | cbn; bv_solve].
  - split.
    + rewrite -Hlength take_app_length.
      apply Z_to_bv_little_endian_to_bv_to_little_endian; [lia | reflexivity].
    + rewrite app_length !length_bv_to_little_endian; lia.
Qed.
Print Assumptions transactions_chain_word_image.
