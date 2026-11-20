Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.All.
Import ListNotations.
Local Open Scope Z_scope.

(* Adjacent pieces of every kind from the base on: a word cell, an
   uninitialised region, a byte array at element type [byte] with a [length]
   fact, one at [bv 8] with a [Z.of_nat] length fact and an explicit list are
   folded into one byte array with its length. *)
Lemma frame_fold_run_mixed `{!islaG Sigma} (a : Z) (v : bv 64) (b1 : list byte)
    (b2 : list (bv 8)) (x y : bv 8) :
  length b1 = 4%nat -> Z.of_nat (length b2) = 2 ->
  a ↦ₘ v -∗ (a + 8) ↦ₘ? 8 -∗ (a + 8 + 8) ↦ₘ∗ b1 -∗ (a + 20) ↦ₘ∗ b2 -∗
  (a + 22) ↦ₘ∗ [x; y] -∗
  ∃ l : list (bv 8), a ↦ₘ∗ l ∗ ⌜length l = 24%nat⌝.
Proof.
  intros H1 H2. iIntros "Hv Hu H1 H2 H3".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_fold_byte_run a.
  iExists _. iFrame. iPureIntro. lia.
Qed.

(* A gap ends the run: the piece after it stays out. *)
Lemma frame_fold_run_gap `{!islaG Sigma} (a : Z) (v : bv 64) :
  a ↦ₘ v -∗ (a + 16) ↦ₘ? 8 -∗
  ∃ l : list (bv 8), a ↦ₘ∗ l ∗ ⌜length l = 8%nat⌝ ∗ (a + 16) ↦ₘ? 8.
Proof.
  iIntros "Hv Hu".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_fold_byte_run a.
  iExists _. iFrame. iPureIntro. lia.
Qed.

(* A piece that starts inside the run (an overlap) is not joined; the
   adjacent piece after the run is. *)
Lemma frame_fold_run_overlap `{!islaG Sigma} (a : Z) (v : bv 64) (b : list (bv 8)) :
  length b = 8%nat ->
  a ↦ₘ v -∗ (a + 4) ↦ₘ∗ b -∗ (a + 8) ↦ₘ? 8 -∗
  ∃ l : list (bv 8), a ↦ₘ∗ l ∗ ⌜length l = 16%nat⌝ ∗ (a + 4) ↦ₘ∗ b.
Proof.
  intros Hb. iIntros "Hv Hb Hu".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_fold_byte_run a.
  iExists _. iFrame. iPureIntro. lia.
Qed.

(* An offset that is not a closed numeral is never computed: the piece at
   [a + 8 + k] stays out even when [k] is zero. *)
Lemma frame_fold_run_symbolic `{!islaG Sigma} (a k : Z) (v : bv 64) :
  k = 0 ->
  a ↦ₘ v -∗ (a + 8 + k) ↦ₘ? 8 -∗
  ∃ l : list (bv 8), a ↦ₘ∗ l ∗ ⌜length l = 8%nat⌝ ∗ (a + 8 + k) ↦ₘ? 8.
Proof.
  intros Hk. iIntros "Hv Hu".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_fold_byte_run a.
  iExists _. iFrame. iPureIntro. lia.
Qed.

(* No piece at the base: the fold refuses. *)
Lemma frame_fold_run_refuses_no_base `{!islaG Sigma} (a : Z) (v : bv 64) :
  (a + 8) ↦ₘ v -∗ (a + 8) ↦ₘ v.
Proof.
  iIntros "Hv".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_fold_byte_run a.
  iExact "Hv".
Qed.

Print Assumptions frame_fold_run_mixed.
Print Assumptions frame_fold_run_gap.
Print Assumptions frame_fold_run_overlap.
Print Assumptions frame_fold_run_symbolic.
Print Assumptions frame_fold_run_refuses_no_base.
