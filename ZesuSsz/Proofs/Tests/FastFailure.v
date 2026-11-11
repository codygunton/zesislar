(* Tests for steps that refuse earlier: the store-lookup head test, the
   binary-nat retry guard, and the pure-fact registration guards. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import ZesuSsz.Automation2.All.

(* The store lookup tests its goal head once, before any alternative. *)
Section FastFailureStoreLookup.
Context `{!islaG Sigma} `{!threadG}.
Lemma fast_failure_store_lookup_head (a : Z) (T : mem_mapsto_kind -> iProp Sigma) :
  find_in_context (FindMemMapsTo a) T ⊢ find_in_context (FindMemMapsTo a) T.
Proof. iIntros "H". ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_lookup_goal. iExact "H". Qed.
Lemma fast_failure_store_lookup_other (P : iProp Sigma) : P ⊢ P.
Proof. iIntros "H". Fail ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_lookup_goal. iExact "H". Qed.
End FastFailureStoreLookup.

(* The binary-nat retry runs only when a natural-number order is present. *)
Section FastFailureNat.
Lemma fast_failure_nat_present (n : nat) (z : Z) : (n < 8)%nat -> (z < 3)%Z -> True.
Proof. intros Hn Hz. ZesuSsz.Automation2.Hooks.zesu_nat_order_present. exact I. Qed.
Lemma fast_failure_nat_absent (z : Z) : (z < 3)%Z -> True.
Proof. intros Hz. Fail ZesuSsz.Automation2.Hooks.zesu_nat_order_present. exact I. Qed.
Lemma fast_failure_nat_alternative (n : nat) : (n < 8)%nat -> (n <= 7)%nat.
Proof. intros Hn. ZesuSsz.Automation2.Hooks.zesu_solve_machine_linear. Qed.
End FastFailureNat.

(* The pure-fact step resolves a registration before its hypothesis scans. *)
Section FastFailurePureFacts.
Context {Sigma : gFunctors}.
Definition fastFailureIntroTarget (n : nat) : iProp Sigma := True%I.
Definition fastFailureAnchorTarget (n : nat) : iProp Sigma := True%I.
Definition fastFailureAnchor (n : nat) : iProp Sigma := True%I.
Definition fastFailurePlainTarget (n : nat) : iProp Sigma := True%I.
Typeclasses Opaque fastFailureIntroTarget fastFailureAnchorTarget fastFailureAnchor
  fastFailurePlainTarget.
#[local] Instance fastFailureIntroTarget_unfold : LithiumUnfold (@fastFailureIntroTarget) := I.
#[local] Instance fastFailureAnchorTarget_unfold : LithiumUnfold (@fastFailureAnchorTarget) := I.
#[local] Instance fastFailureAnchor_unfold : LithiumUnfold (@fastFailureAnchor) := I.
#[local] Instance fastFailurePlainTarget_unfold : LithiumUnfold (@fastFailurePlainTarget) := I.
#[local] Instance fastFailureIntroRegistration n :
  ZesuSsz.Automation.Hooks.ZesuPureFactIntro (fastFailureIntroTarget n) True%I.
Proof. unfold ZesuSsz.Automation.Hooks.ZesuPureFactIntro, fastFailureIntroTarget. iIntros "_". done. Qed.
#[local] Instance fastFailureAnchorRegistration n :
  ZesuSsz.Automation.Hooks.ZesuPureFactAnchor (fastFailureAnchorTarget n) (fastFailureAnchor n) True%I.
Proof.
  unfold ZesuSsz.Automation.Hooks.ZesuPureFactAnchor, ZesuSsz.Automation.Hooks.ZesuPureFactIntro,
    fastFailureAnchorTarget. iIntros "_". done.
Qed.
Lemma fast_failure_pure_fact_guards (n : nat) : True.
Proof.
  ZesuSsz.Automation2.Hooks.zesu_pure_fact_intro_registered (fastFailureIntroTarget n).
  ZesuSsz.Automation2.Hooks.zesu_pure_fact_anchor_registered (fastFailureAnchorTarget n).
  Fail ZesuSsz.Automation2.Hooks.zesu_pure_fact_intro_registered (fastFailureAnchorTarget n).
  Fail ZesuSsz.Automation2.Hooks.zesu_pure_fact_anchor_registered (fastFailurePlainTarget n).
  exact I.
Qed.
Lemma fast_failure_pure_fact_intro_route (n : nat) : True ⊢ fastFailureIntroTarget n.
Proof. iIntros "_". ZesuSsz.Automation2.Hooks.zesu_pure_fact_hints_if_enabled. by iPureIntro. Qed.
Lemma fast_failure_pure_fact_anchor_route (n : nat) : fastFailureAnchor n ⊢ fastFailureAnchorTarget n.
Proof. iIntros "H". ZesuSsz.Automation2.Hooks.zesu_pure_fact_hints_if_enabled. by iPureIntro. Qed.
Lemma fast_failure_pure_fact_none (n : nat) : fastFailureAnchor n ⊢ fastFailurePlainTarget n.
Proof.
  iIntros "H". Fail ZesuSsz.Automation2.Hooks.zesu_pure_fact_hints_if_enabled.
  unfold fastFailurePlainTarget. by iPureIntro.
Qed.
End FastFailurePureFacts.
