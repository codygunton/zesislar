Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.AltFlFreeBlockEntries.
Require Import ZesuSsz.Contracts.AbiBytes.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma freeWord64BytesEncoding (value : Z) :
  bv_to_little_endian 8 8 value = word64Bytes value.
Proof.
  unfold word64Bytes, bv_to_little_endian, Z_to_little_endian.
  cbn [List.seq List.map Z.iter]. cbn.
  rewrite !Z.shiftr_shiftr; try lia.
  cbn. rewrite Z.shiftr_0_r. rewrite !Z.land_ones; try lia.
  repeat apply f_equal2; try reflexivity; apply bv_eq;
    rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn;
    rewrite Z.mod_mod; try reflexivity; lia.
Qed.

Lemma freeSavedReturnDecoder args frameBytes :
  freeSavedFrameFacts args frameBytes ->
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 frameBytes))) =
    Z_to_bv 64 (freeReturnAddress args).
Proof.
  unfold freeSavedFrameFacts. intros ->.
  rewrite <- !freeWord64BytesEncoding.
  rewrite drop_app_length'.
  2: { rewrite length_bv_to_little_endian; done. }
  rewrite take_ge.
  2: { rewrite length_bv_to_little_endian; done. }
  rewrite little_endian_to_bv_to_little_endian; last lia.
  change (Z_to_bv 64 (freeReturnAddress args mod bv_modulus 64) = Z_to_bv 64 (freeReturnAddress args)).
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 (bv_wrap 64 (freeReturnAddress args)) = bv_wrap 64 (freeReturnAddress args)).
  apply bv_wrap_idemp.
Qed.

Lemma freeBlockCoreReturnDecoder `{!islaG Sigma} `{!threadG}
    args (x1 x2 x8 x10 x11 x12 x13 x14 : bv 64)
    (bufferBytes listBytes frameBytes : list byte) :
  freeBlockCore args x1 x2 x8 x10 x11 x12 x13 x14
    bufferBytes listBytes frameBytes ⊢
  ⌜Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 frameBytes))) =
    Z_to_bv 64 (freeReturnAddress args)⌝.
Proof.
  unfold freeBlockCore.
  iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hcore & _)".
  iPureIntro. apply freeSavedReturnDecoder.
  destruct Hcore as (_ & _ & _ & _ & _ & _ & _ & Hframe). exact Hframe.
Qed.
