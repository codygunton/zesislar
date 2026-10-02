Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Sets.call.
From Coq Require Import Lists.List.
Import ListNotations.

Definition loadWordRaw `{!islaG Sigma} `{!threadG}
    (address : Z) (value : bv 64) : iProp Sigma := (address ↦ₘ value ∗ True)%I.
Global Instance : LithiumUnfold (@loadWordRaw) := I.
Global Typeclasses Opaque loadWordRaw.
Definition loadWordSeal `{!islaG Sigma} `{!threadG}
    (address : Z) (value : bv 64) := loadWordRaw address value.
Lemma loadWordSeal_unfold `{!islaG Sigma} `{!threadG} address value :
  loadWordSeal address value ⊣⊢ loadWordRaw address value.
Proof. done. Qed.
Global Opaque loadWordSeal.
Global Instance loadWordCoverage `{!islaG Sigma} `{!threadG} address value :
  ZesuSealed (loadWordSeal address value) (loadWordRaw address value) [] [] :=
  loadWordSeal_unfold address value.

Lemma test_load_word_seal `{!islaG Sigma} `{!threadG}
    (address : Z) (value : bv 64) :
  loadWordSeal address value -∗
  ∃ y : bv 64 *ₗ (), (address ↦ₘ y.1ₗ ∗ True)%I.
Proof.
  iIntros "Hmemory".
  zesu_rule_set_v2_steps.
  iExists (value, tt)ₗ. iFrame.
Qed.
Print Assumptions test_load_word_seal.

Lemma test_load_word_raw `{!islaG Sigma} `{!threadG}
    (address : Z) (value : bv 64) :
  loadWordRaw address value -∗
  ∃ y : bv 64 *ₗ (), (address ↦ₘ y.1ₗ ∗ True)%I.
Proof.
  iIntros "Hmemory".
  zesu_rule_set_v2_steps.
  iExists (value, tt)ₗ. iFrame.
Qed.
Print Assumptions test_load_word_raw.

Definition loadArrayRaw `{!islaG Sigma} `{!threadG}
    (address : Z) (value : list (bv 64)) : iProp Sigma := (address ↦ₘ∗ value ∗ True)%I.
Global Instance : LithiumUnfold (@loadArrayRaw) := I.
Global Typeclasses Opaque loadArrayRaw.
Definition loadArraySeal `{!islaG Sigma} `{!threadG}
    (address : Z) (value : list (bv 64)) := loadArrayRaw address value.
Lemma loadArraySeal_unfold `{!islaG Sigma} `{!threadG} address value :
  loadArraySeal address value ⊣⊢ loadArrayRaw address value.
Proof. done. Qed.
Global Opaque loadArraySeal.
Global Instance loadArrayCoverage `{!islaG Sigma} `{!threadG} address value :
  ZesuSealed (loadArraySeal address value) (loadArrayRaw address value) [] [] :=
  loadArraySeal_unfold address value.

Lemma test_load_array_seal `{!islaG Sigma} `{!threadG}
    (address : Z) (value : list (bv 64)) :
  loadArraySeal address value -∗
  ∃ y : list (bv 64) *ₗ (), (address ↦ₘ∗ y.1ₗ ∗ True)%I.
Proof.
  iIntros "Hmemory".
  zesu_rule_set_v2_steps.
  iExists (value, tt)ₗ. iFrame.
Qed.
Print Assumptions test_load_array_seal.

Lemma test_load_array_raw `{!islaG Sigma} `{!threadG}
    (address : Z) (value : list (bv 64)) :
  loadArrayRaw address value -∗
  ∃ y : list (bv 64) *ₗ (), (address ↦ₘ∗ y.1ₗ ∗ True)%I.
Proof.
  iIntros "Hmemory".
  zesu_rule_set_v2_steps.
  iExists (value, tt)ₗ. iFrame.
Qed.
Print Assumptions test_load_array_raw.

