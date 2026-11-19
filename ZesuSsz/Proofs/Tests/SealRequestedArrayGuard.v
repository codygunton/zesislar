Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Guard of zesu_seal_requested_array: it seals an opened request only when
   the context holds the sealed array at the requested base. *)
Section seal_guard_tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* Fires: the context holds the sealed array at the requested base, under
     the dummy existential a successor entry is stated with. *)
  Lemma seal_guard_fires (a : Z) (l : list (bv 8)) (P : iProp Sigma) :
    a ↦ₘ∗ l -∗ P -∗
    ∃ _ : unit, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗ P.
  Proof.
    iIntros "Harray HP".
    zesu_seal_requested_array.
    iExists tt. iFrame "Harray HP".
  Qed.

  (* Skipped: the context holds the bytes as cells (an opened frame), so the
     request stays opened and the rebuild rule assembles it from the cells. *)
  Lemma seal_guard_skips_cells (a : Z) (b0 b1 : bv 8) (P : iProp Sigma) :
    isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) [b0; b1] -∗ P -∗
    ∃ _ : unit, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) [b0; b1] ∗ P.
  Proof.
    iIntros "Harray HP".
    progress ZesuSsz.Automation2.ResourceGroups.zesu_open_nested_existential_packages.
    Fail zesu_seal_requested_array.
    zesu_block2.
  Qed.

  (* Skipped: the sealed array in the context sits at another base. *)
  Lemma seal_guard_skips_other_base (a c : Z) (l : list (bv 8)) (P : iProp Sigma) :
    c ↦ₘ∗ l -∗
    (isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗ P) -∗
    isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗ P.
  Proof.
    iIntros "Hother Hrequested".
    Fail zesu_seal_requested_array.
    iExact "Hrequested".
  Qed.

  (* Skipped: the sealed array at the requested base is stated with other
     bytes (here equal only up to a lemma; in a block, a store updated part
     of it). The request stays opened, so its cells are looked up in the held
     array instead of leaving an equation between the two byte lists. *)
  Lemma seal_guard_skips_other_bytes (a : Z) (l : list (bv 8)) (P : iProp Sigma) :
    a ↦ₘ∗ (l ++ []) -∗ P -∗
    ∃ _ : unit, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗ P.
  Proof.
    iIntros "Harray HP".
    Fail zesu_seal_requested_array.
    iEval (rewrite app_nil_r) in "Harray".
    zesu_seal_requested_array.
    iExists tt. iFrame "Harray HP".
  Qed.
End seal_guard_tests.
