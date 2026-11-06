Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith.
From iris.base_logic.lib Require Import iprop.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteArrayAssembly.
Import ListNotations.
Require Import ZesuSsz.Automation.All.
Open Scope Z_scope.
Section Controls.
Context (Sigma : gFunctors) (islaG0 : islaG Sigma).
#[local] Existing Instance islaG0.

Lemma assembly_two (address : Z) (fraction : dfrac) (first second : bv 8) :
  address ↦ₘ{fraction} first -∗ (address + 1) ↦ₘ{fraction} second -∗
  address ↦ₘ{fraction}∗ [first; second].
Proof.
  iIntros "Hfirst Hsecond". zesu_byte_array_assemble.
Qed.

Lemma assembly_three (address : Z) (fraction : dfrac) (first second third : bv 8) :
  address ↦ₘ{fraction} first -∗ (address + 1) ↦ₘ{fraction} second -∗
  (address + 2) ↦ₘ{fraction} third -∗ address ↦ₘ{fraction}∗ [first; second; third].
Proof.
  iIntros "Hfirst Hsecond Hthird". zesu_byte_array_assemble.
Qed.

Lemma assembly_tail (address : Z) (fraction : dfrac) (byte : bv 8) (tail : list (bv 8)) :
  address ↦ₘ{fraction} byte -∗ (address + 1) ↦ₘ{fraction}∗ tail -∗
  address ↦ₘ{fraction}∗ (byte :: tail).
Proof.
  iIntros "Hbyte Htail". zesu_byte_array_assemble.
Qed.

Lemma assembly_fraction_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (byte : bv 8),
    ⊢ (address ↦ₘ{DfracDiscarded} byte -∗ address ↦ₘ∗ [byte])%I) by
    (intros address byte; iIntros "Hbyte"; zesu_byte_array_assemble)).
  exact I.
Qed.

Lemma assembly_address_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (byte : bv 8),
    ⊢ ((address + 1) ↦ₘ byte -∗ address ↦ₘ∗ [byte])%I) by
    (intros address byte; iIntros "Hbyte"; zesu_byte_array_assemble)).
  exact I.
Qed.

Lemma assembly_order_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (first second : bv 8),
    ⊢ (address ↦ₘ first -∗ (address + 1) ↦ₘ second -∗
       address ↦ₘ∗ [second; first])%I) by
    (intros address first second; iIntros "Hfirst Hsecond"; zesu_byte_array_assemble)).
  exact I.
Qed.
End Controls.
