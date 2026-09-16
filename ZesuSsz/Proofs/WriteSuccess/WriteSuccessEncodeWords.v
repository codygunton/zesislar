Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
From Coq Require Import Lists.List ZArith.ZArith Lia.

Open Scope Z_scope.

Lemma writeSuccessEncodeLe_split n m low high :
  0 <= low < 256 ^ Z.of_nat n ->
  writeSuccessEncodeLe (n + m) (low + 256 ^ Z.of_nat n * high) =
  writeSuccessEncodeLe n low ++ writeSuccessEncodeLe m high.
Proof.
  revert low. induction n as [|n IH]; intros low Hlow.
  - change (0 <= low < 1) in Hlow. replace low with 0 by lia.
    replace (256 ^ Z.of_nat 0) with 1 by reflexivity.
    rewrite Z.mul_1_l Z.add_0_l. reflexivity.
  - rewrite Nat2Z.inj_succ Z.pow_succ_r in Hlow |- *; [|lia..].
    replace (low + 256 * 256 ^ Z.of_nat n * high) with
      (low + (256 ^ Z.of_nat n * high) * 256) by ring.
    change (S n + m)%nat with (S (n + m))%nat.
    cbn [writeSuccessEncodeLe]. rewrite Z.mod_add; [|lia].
    rewrite Z.div_add; [|lia].
    cbn [app]. f_equal. apply IH.
    have Hp : 0 < 256 ^ Z.of_nat n by apply Z.pow_pos_nonneg; lia.
    split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; nia.
Qed.

Lemma writeSuccessEncodeU128_words (low high : bv 64) :
  writeSuccessEncodeU128 (bv_unsigned low + 2 ^ 64 * bv_unsigned high) =
  writeSuccessEncodeU64 (bv_unsigned low) ++
  writeSuccessEncodeU64 (bv_unsigned high).
Proof.
  change (writeSuccessEncodeLe (8 + 8)
    (bv_unsigned low + 256 ^ Z.of_nat 8 * bv_unsigned high) =
    writeSuccessEncodeLe 8 (bv_unsigned low) ++
    writeSuccessEncodeLe 8 (bv_unsigned high)).
  apply writeSuccessEncodeLe_split. bv_solve.
Qed.

Print Assumptions writeSuccessEncodeLe_split.
Print Assumptions writeSuccessEncodeU128_words.

Lemma writeSuccessEncodeU256_words (w0 w1 w2 w3 : bv 64) :
  writeSuccessEncodeU256
    (bv_unsigned w0 + 2 ^ 64 *
      (bv_unsigned w1 + 2 ^ 64 * (bv_unsigned w2 + 2 ^ 64 * bv_unsigned w3))) =
  writeSuccessEncodeU64 (bv_unsigned w0) ++
  writeSuccessEncodeU64 (bv_unsigned w1) ++
  writeSuccessEncodeU64 (bv_unsigned w2) ++
  writeSuccessEncodeU64 (bv_unsigned w3).
Proof.
  rewrite /writeSuccessEncodeU256.
  change 32%nat with (8 + 24)%nat.
  replace (2 ^ 64)%Z with (256 ^ Z.of_nat 8)%Z by reflexivity.
  rewrite writeSuccessEncodeLe_split; [|bv_solve].
  change (writeSuccessEncodeLe 24) with (writeSuccessEncodeLe (8 + 16)).
  rewrite writeSuccessEncodeLe_split; [|bv_solve].
  change (writeSuccessEncodeLe 16) with (writeSuccessEncodeLe (8 + 8)).
  rewrite writeSuccessEncodeLe_split; [|bv_solve].
  reflexivity.
Qed.

Print Assumptions writeSuccessEncodeU256_words.

Lemma writeSuccessPrivateEncodeU64 (word : bv 64) :
  writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned word)) =
  bv_to_little_endian 8 8 (bv_unsigned word).
Proof.
  rewrite /writeSuccessPrivateBytes /writeSuccessEncodeU64
    /writeSuccessEncodeLe /bv_to_little_endian /=.
  rewrite !Z.land_ones; [|lia..].
  rewrite !Z.shiftr_div_pow2; [|lia..].
  reflexivity.
Qed.

Print Assumptions writeSuccessPrivateEncodeU64.
