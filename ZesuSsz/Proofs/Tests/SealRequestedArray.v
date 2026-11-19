Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Section seal_tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* A successor entry requests the opened array; the context holds the
     sealed one, which does not frame it until the request is sealed. *)
  Lemma seal_requested_array_sep (a : Z) (l : list (bv 8)) (P : iProp Sigma) :
    a ↦ₘ∗ l -∗ P -∗ isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗ P.
  Proof.
    iIntros "Harray HP".
    Fail iFrame "Harray".
    zesu_seal_requested_array.
    iFrame "Harray HP".
  Qed.

  (* The request under an existential is sealed too. *)
  Lemma seal_requested_array_exists (a : Z) (l : list (bv 8)) :
    a ↦ₘ∗ l -∗ ∃ n : Z, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗ ⌜n = 0⌝.
  Proof.
    iIntros "Harray".
    Fail iExists 0; iFrame "Harray".
    zesu_seal_requested_array.
    iExists 0. iFrame "Harray". done.
  Qed.

  (* A sealed request is left alone. *)
  Lemma seal_requested_array_sealed (a : Z) (l : list (bv 8)) (P : iProp Sigma) :
    a ↦ₘ∗ l -∗ P -∗ a ↦ₘ∗ l ∗ P.
  Proof.
    iIntros "Harray HP".
    Fail zesu_seal_requested_array.
    iFrame "Harray HP".
  Qed.
End seal_tests.
