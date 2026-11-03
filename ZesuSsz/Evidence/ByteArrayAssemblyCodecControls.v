Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith.
From iris.base_logic.lib Require Import iprop.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteArrayAssemblyCodec.
Import ListNotations.
Open Scope Z_scope.
Section Controls.
Context (Sigma : gFunctors) (islaG0 : islaG Sigma).
#[local] Existing Instance islaG0.

Lemma assembly_codec_two (address : Z) (fraction : dfrac) (word : bv 64) :
  address ↦ₘ{fraction} Z_to_bv 8 (Z.land (bv_unsigned word) (Z.ones 8)) -∗
  (address + 1) ↦ₘ{fraction} Z_to_bv 8 (Z.land (bv_unsigned word ≫ 8) (Z.ones 8)) -∗
  address ↦ₘ{fraction}∗ bv_to_little_endian 2 8 (bv_unsigned word).
Proof.
  iIntros "Hfirst Hsecond". zesu_byte_array_assemble_codec.
Qed.

Lemma assembly_codec_eight (address : Z) (fraction : dfrac) (word : bv 64) :
  address ↦ₘ{fraction} Z_to_bv 8 (Z.land (bv_unsigned word) (Z.ones 8)) -∗
  (address + 1) ↦ₘ{fraction} Z_to_bv 8 (Z.land (bv_unsigned word ≫ 8) (Z.ones 8)) -∗
  (address + 2) ↦ₘ{fraction} Z_to_bv 8 (Z.land ((bv_unsigned word ≫ 8) ≫ 8) (Z.ones 8)) -∗
  (address + 3) ↦ₘ{fraction} Z_to_bv 8 (Z.land (((bv_unsigned word ≫ 8) ≫ 8) ≫ 8) (Z.ones 8)) -∗
  (address + 4) ↦ₘ{fraction} Z_to_bv 8 (Z.land ((((bv_unsigned word ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8)) -∗
  (address + 5) ↦ₘ{fraction} Z_to_bv 8 (Z.land (((((bv_unsigned word ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8)) -∗
  (address + 6) ↦ₘ{fraction} Z_to_bv 8 (Z.land ((((((bv_unsigned word ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8)) -∗
  (address + 7) ↦ₘ{fraction} Z_to_bv 8 (Z.land (((((((bv_unsigned word ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) (Z.ones 8)) -∗
  address ↦ₘ{fraction}∗ bv_to_little_endian (Z.of_nat 8%nat) 8 (bv_unsigned word).
Proof.
  iIntros "H0 H1 H2 H3 H4 H5 H6 H7". zesu_byte_array_assemble_codec.
Qed.

Lemma assembly_codec_symbolic_count_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (count address : Z) (word : bv 64),
    ⊢ (address ↦ₘ Z_to_bv 8 (Z.land (bv_unsigned word) (Z.ones 8)) -∗
       address ↦ₘ∗ bv_to_little_endian count 8 (bv_unsigned word))%I) by
    (intros count address word; iIntros "Hbyte"; zesu_byte_array_assemble_codec)).
  exact I.
Qed.

Lemma assembly_codec_fraction_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (word : bv 64),
    ⊢ (address ↦ₘ{DfracDiscarded} Z_to_bv 8 (Z.land (bv_unsigned word) (Z.ones 8)) -∗
       address ↦ₘ∗ bv_to_little_endian 1 8 (bv_unsigned word))%I) by
    (intros address word; iIntros "Hbyte"; zesu_byte_array_assemble_codec)).
  exact I.
Qed.

Lemma assembly_codec_address_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (word : bv 64),
    ⊢ ((address + 1) ↦ₘ Z_to_bv 8 (Z.land (bv_unsigned word) (Z.ones 8)) -∗
       address ↦ₘ∗ bv_to_little_endian 1 8 (bv_unsigned word))%I) by
    (intros address word; iIntros "Hbyte"; zesu_byte_array_assemble_codec)).
  exact I.
Qed.

Lemma assembly_codec_order_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (word : bv 64),
    ⊢ (address ↦ₘ Z_to_bv 8 (Z.land (bv_unsigned word ≫ 8) (Z.ones 8)) -∗
       (address + 1) ↦ₘ Z_to_bv 8 (Z.land (bv_unsigned word) (Z.ones 8)) -∗
       address ↦ₘ∗ bv_to_little_endian 2 8 (bv_unsigned word))%I) by
    (intros address word; iIntros "Hfirst Hsecond"; zesu_byte_array_assemble_codec)).
  exact I.
Qed.
End Controls.
