Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Section chain_tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* A byte array opened into one chain hypothesis: the lookup sees only
     whole cells, so it fails until the chain is split. *)
  Lemma memory_cell_chain_split (a0 a1 a2 : Z) (b0 b1 b2 : bv 8) :
    (a0 ↦ₘ b0 ∗ a1 ↦ₘ b1 ∗ a2 ↦ₘ b2 ∗ emp) -∗
    find_in_context (FindMemMapsTo a1) (fun _ => True)%I.
  Proof.
    iIntros "Hchain".
    Fail liFindInContext.
    zesu_split_memory_cell_chain.
    liFindInContext. done.
  Qed.

  (* The step runs the split before the memory lookup. *)
  Lemma memory_cell_chain_step (a0 a1 : Z) (b0 b1 : bv 8) :
    (a0 ↦ₘ b0 ∗ a1 ↦ₘ b1) -∗
    find_in_context (FindMemMapsTo a1) (fun _ => True)%I.
  Proof.
    iIntros "Hchain".
    Fail liFindInContext.
    zesu_liAStep.
    liFindInContext. done.
  Qed.

  (* Only a memory lookup splits a chain. *)
  Lemma memory_cell_chain_other_goal (a0 a1 : Z) (b0 b1 : bv 8) :
    (a0 ↦ₘ b0 ∗ a1 ↦ₘ b1) -∗ (a0 ↦ₘ b0 ∗ a1 ↦ₘ b1).
  Proof.
    iIntros "Hchain".
    Fail zesu_split_memory_cell_chain.
    iExact "Hchain".
  Qed.

  (* Without a chain hypothesis the rule makes no progress. *)
  Lemma memory_cell_chain_single (a0 : Z) (b0 : bv 8) :
    a0 ↦ₘ b0 -∗ find_in_context (FindMemMapsTo a0) (fun _ => True)%I.
  Proof.
    iIntros "Hcell".
    Fail zesu_split_memory_cell_chain.
    liFindInContext. done.
  Qed.
End chain_tests.

(* Without the split, the step does not reach the cell. *)
#[local] Ltac ZesuSsz.Automation2.Hooks.zesu_split_memory_cell_chain ::=
  fail "memory cell chain split disabled".

Section chain_ablation.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma memory_cell_chain_needs_split (a0 a1 : Z) (b0 b1 : bv 8) :
    (a0 ↦ₘ b0 ∗ a1 ↦ₘ b1) -∗
    find_in_context (FindMemMapsTo a1) (fun _ => True)%I.
  Proof.
    iIntros "Hchain".
    Fail zesu_liAStep; liFindInContext.
    iDestruct "Hchain" as "[H0 H1]".
    liFindInContext. done.
  Qed.
End chain_ablation.
