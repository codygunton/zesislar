Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.BitvectorFacts.
From Coq Require Import ZArith NArith.
From stdpp Require Import bitvector.tactics.
Local Open Scope Z_scope.

Lemma masked_payload_plain (byte : bv 8) (limit : bv 64) :
  129 <= bv_unsigned byte <= 183 ->
  ~ (bv_signed (bv_zero_extend 128
      (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127))) >=
    bv_signed (bv_zero_extend 128 limit)) ->
  bv_unsigned byte - 128 < bv_unsigned limit.
Proof. intros [Hlower Hupper] Hbranch. BitvectorFacts.zesu_source_biased_mask_goal. Qed.

Lemma masked_payload_bias (byte : bv 8) (limit : bv 64) :
  184 <= bv_unsigned byte <= 191 ->
  ~ (bv_signed (bv_zero_extend 128
      (bv_and (bv_add (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 73)) (BV 64 255))) >=
    bv_signed (bv_zero_extend 128 limit)) ->
  bv_unsigned byte - 183 < bv_unsigned limit.
Proof. intros [Hlower Hupper] Hbranch. BitvectorFacts.zesu_source_biased_mask_goal. Qed.

Lemma masked_payload_other_bias (byte : bv 8) (limit : bv 64) :
  192 <= bv_unsigned byte <= 247 ->
  ~ (bv_signed (bv_zero_extend 128
      (bv_and (bv_add (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 64)) (BV 64 255))) >=
    bv_signed (bv_zero_extend 128 limit)) ->
  bv_unsigned byte - 192 < bv_unsigned limit.
Proof. intros [Hlower Hupper] Hbranch. BitvectorFacts.zesu_source_biased_mask_goal. Qed.

Lemma masked_payload_last_window (byte : bv 8) (limit : bv 64) :
  248 <= bv_unsigned byte <= 255 ->
  ~ (bv_signed (bv_zero_extend 128
      (bv_and (bv_add (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 9)) (BV 64 255))) >=
    bv_signed (bv_zero_extend 128 limit)) ->
  bv_unsigned byte - 247 < bv_unsigned limit.
Proof. intros [Hlower Hupper] Hbranch. BitvectorFacts.zesu_source_biased_mask_goal. Qed.

Lemma masked_payload_symbolic_mask_refuses (byte : bv 8) (limit mask : bv 64) :
  192 <= bv_unsigned byte <= 247 ->
  ~ (bv_signed (bv_zero_extend 128
      (bv_and (bv_add (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 64)) mask)) >=
    bv_signed (bv_zero_extend 128 limit)) -> True.
Proof.
  intros [Hlower Hupper] Hbranch.
  tryif (assert (Hbad : bv_unsigned byte - 192 < bv_unsigned limit) by
    BitvectorFacts.zesu_source_biased_mask_goal)
  then fail 100 "The symbolic mask passed closed-term validation."
  else exact I.
Qed.
