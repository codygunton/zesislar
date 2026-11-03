Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpatialResourceConsumer.
Require Import isla.riscv64.riscv64.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics environments.
From Coq Require Import List ZArith.
Import ListNotations.
Require Import ZesuSsz.Automation.All.
Open Scope Z_scope.

Definition SpatialBytes : Type := list (bv 8).

Section Controls.
Context (Sigma : gFunctors) (G : islaG Sigma).
#[local] Existing Instance G.

Lemma spatial_alias_owner : forall (address : Z) (fraction : dfrac) (bytes : SpatialBytes) (K : iProp Sigma),
  ⊢ (address ↦ₘ{fraction}∗ bytes ∗ K -∗
   ∃ x : li_prod SpatialBytes unit,
     address ↦ₘ{fraction}∗ li_fst x ∗ K ∗ ⌜li_fst x = bytes⌝)%I.
Proof.
  intros address fraction bytes K.
  iIntros "[Harray HK]".
  SpatialResourceConsumer.zesu_spatial_consume_owners
    ltac:(fun _ => idtac) ltac:(fun _ => try (iPureIntro; reflexivity)).
Qed.

Lemma spatial_owner_address : forall (left right : Z) (fraction : dfrac) (xs ys : SpatialBytes),
  ⊢ (left ↦ₘ{fraction}∗ xs ∗ right ↦ₘ{fraction}∗ ys -∗
   ∃ x : li_prod SpatialBytes unit,
     right ↦ₘ{fraction}∗ li_fst x ∗ left ↦ₘ{fraction}∗ xs ∗ ⌜li_fst x = ys⌝)%I.
Proof.
  intros left right fraction xs ys.
  iIntros "[Hleft Hright]".
  SpatialResourceConsumer.zesu_spatial_consume_owners
    ltac:(fun _ => idtac) ltac:(fun _ => try (iPureIntro; reflexivity)).
Qed.

Lemma spatial_owner_fraction_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (byte : bv 8),
    ⊢ (address ↦ₘ{DfracDiscarded}∗ [byte] -∗
      ∃ x : li_prod SpatialBytes unit,
        address ↦ₘ∗ li_fst x ∗ ⌜li_fst x = [byte]⌝)%I) by
    (intros address byte; iIntros "Harray";
     solve [SpatialResourceConsumer.zesu_spatial_consume_owners
       ltac:(fun _ => idtac) ltac:(fun _ => try (iPureIntro; reflexivity))])).
  exact I.
Qed.

Lemma spatial_owner_address_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (byte : bv 8),
    ⊢ ((address + 1) ↦ₘ∗ [byte] -∗
      ∃ x : li_prod SpatialBytes unit,
        address ↦ₘ∗ li_fst x ∗ ⌜li_fst x = [byte]⌝)%I) by
    (intros address byte; iIntros "Harray";
     solve [SpatialResourceConsumer.zesu_spatial_consume_owners
       ltac:(fun _ => idtac) ltac:(fun _ => try (iPureIntro; reflexivity))])).
  exact I.
Qed.

Lemma spatial_owner_order_refuses : True.
Proof.
  assert_fails ltac:(assert (Hbad : forall (address : Z) (first second : bv 8),
    ⊢ (address ↦ₘ∗ [first; second] -∗
      ∃ x : li_prod SpatialBytes unit,
        address ↦ₘ∗ li_fst x ∗ ⌜li_fst x = [second; first]⌝)%I) by
    (intros address first second; iIntros "Harray";
     solve [SpatialResourceConsumer.zesu_spatial_consume_owners
       ltac:(fun _ => idtac) ltac:(fun _ => try (iPureIntro; reflexivity))])).
  exact I.
Qed.

End Controls.
