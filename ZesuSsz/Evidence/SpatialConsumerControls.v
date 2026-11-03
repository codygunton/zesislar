Require Import ZesuSsz.Automation.All.
Require Import lithium.interpreter lithium.pure_definitions.
Require Import ZesuSsz.Automation.SpatialConsumer.
From Coq Require Import ZArith.
From stdpp Require Import bitvector.tactics decidable.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics environments.
Local Open Scope Z_scope.

Lemma spatial_correlated_choice (Sigma : gFunctors) (P Q : Z -> Prop)
    (a b : Z) (Ha : P a) (Hqa : Q a) (Hb : P b) :
  ((emp : iProp Sigma) ⊢ ∃ x : li_prod Z unit,
    ⌜P (li_fst x)⌝ ∗ ⌜Q (li_fst x)⌝)%I.
Proof.
  iIntros "_".
  SpatialConsumer.zesu_spatial_pack_package
    ltac:(SpatialConsumer.zesu_spatial_finish_package).
Qed.

Lemma spatial_correlation_refuses (Sigma : gFunctors) (P Q : Z -> Prop)
    (a b : Z) (Ha : P a) (Hqb : Q b) : True.
Proof.
  Fail assert (test : ((emp : iProp Sigma) ⊢ ∃ x : li_prod Z unit,
      ⌜P (li_fst x)⌝ ∗ ⌜Q (li_fst x)⌝)%I) by
    (iIntros "_"; SpatialConsumer.zesu_spatial_pack_package
      ltac:(SpatialConsumer.zesu_spatial_finish_package)).
  exact I.
Qed.

Lemma spatial_boolean_view (P : Prop) `{Decision P} (HP : P) :
  bool_decide P = true.
Proof. SpatialConsumer.zesu_spatial_finish_fact. Qed.

Lemma spatial_negative_boolean_view (P : Prop) `{Decision P} (HP : ~ P) :
  negb (bool_decide P) = true.
Proof. SpatialConsumer.zesu_spatial_finish_fact. Qed.

Lemma spatial_mask_view (word : bv 64)
    (Hmask : Z.land (bv_unsigned word) 131072 = 0) :
  bv_and word (BV 64 131072) = BV 64 0.
Proof. SpatialConsumer.zesu_spatial_mask_fact. Qed.

Lemma spatial_mask_missing_fact_refuses (word : bv 64) : True.
Proof.
  Fail assert (test : bv_and word (BV 64 131072) = BV 64 0) by
    SpatialConsumer.zesu_spatial_mask_fact.
  exact I.
Qed.

Lemma spatial_mask_changed_value_refuses (word other : bv 64)
    (Hmask : Z.land (bv_unsigned other) 131072 = 0) : True.
Proof.
  Fail assert (test : bv_and word (BV 64 131072) = BV 64 0) by
    SpatialConsumer.zesu_spatial_mask_fact.
  exact I.
Qed.

Lemma spatial_symbolic_mask_refuses (word mask : bv 64)
    (Hmask : Z.land (bv_unsigned word) (bv_unsigned mask) = 0) : True.
Proof.
  Fail assert (test : bv_and word mask = BV 64 0) by
    SpatialConsumer.zesu_spatial_mask_fact.
  exact I.
Qed.

Lemma spatial_count_view (byte : bv 8) (length_word : bv 64)
    (Hlower : 128 <= bv_unsigned byte)
    (Hguard : ~ bv_signed (bv_zero_extend 128
      (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127))) >=
      bv_signed (bv_zero_extend 128 length_word)) :
  bv_unsigned byte - 128 < bv_unsigned length_word.
Proof. SpatialConsumer.zesu_spatial_count_fact. Qed.

Lemma spatial_count_missing_bound_refuses (byte : bv 8) (length_word : bv 64)
    (Hguard : ~ bv_signed (bv_zero_extend 128
      (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127))) >=
      bv_signed (bv_zero_extend 128 length_word)) : True.
Proof.
  Fail assert (test : bv_unsigned byte - 128 < bv_unsigned length_word) by
    SpatialConsumer.zesu_spatial_count_fact.
  exact I.
Qed.

Lemma spatial_symbolic_bias_refuses (byte : bv 8) (length_word : bv 64)
    (bias : Z) (Hlower : 128 <= bv_unsigned byte)
    (Hguard : ~ bv_signed (bv_zero_extend 128
      (bv_and (bv_and (bv_sign_extend 64 byte) (BV 64 255)) (BV 64 127))) >=
      bv_signed (bv_zero_extend 128 length_word)) : True.
Proof.
  Fail assert (test : bv_unsigned byte - bias < bv_unsigned length_word) by
    SpatialConsumer.zesu_spatial_count_fact.
  exact I.
Qed.
