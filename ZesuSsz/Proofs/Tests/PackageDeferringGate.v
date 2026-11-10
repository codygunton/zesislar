Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The package step runs its deferring route only after the source route
   refuses a fixed fact. Here a marker takes the place of the deferring
   route, so a run leaves `PackageDeferringRan` in the context. The real
   route is checked by PackageResidualTier.v. *)
Inductive PackageDeferringRan : Prop := package_deferring_ran.

Ltac package_deferring_marker :=
  pose proof package_deferring_ran as HpackageDeferringRan.

Ltac package_deferring_marked :=
  idtac; match goal with _ : PackageDeferringRan |- _ => idtac end.

Definition package_gate_fact_aux : seal (fun n : Z => 0 <= n). Proof. by eexists. Qed.
Definition package_gate_fact (n : Z) : Prop := package_gate_fact_aux.(unseal) n.

(* A spatial failure in a large context: the package asks for an array at
   an address that nothing owns, and its fixed fact is provable. The cascade
   fails on the array, so the deferring route does not run. *)
Lemma package_spatial_failure_skips_deferring `{!islaG Sigma} `{!threadG}
    (a b : Z) (bytes : list (bv 8)) (w : bv 64) (n : Z) (K : iProp Sigma)
    (Hmask : bv_and w (BV 64 131072) = BV 64 0) (Hn : 0 <= n)
    (Hcontext1 : n + 1 <= n + 2)
    (Hcontext2 : n + 2 <= n + 3)
    (Hcontext3 : n + 3 <= n + 4)
    (Hcontext4 : n + 4 <= n + 5)
    (Hcontext5 : n + 5 <= n + 6)
    (Hcontext6 : n + 6 <= n + 7)
    (Hcontext7 : n + 7 <= n + 8)
    (Hcontext8 : n + 8 <= n + 9)
    (Hcontext9 : n + 9 <= n + 10)
    (Hcontext10 : n + 10 <= n + 11)
    (Hcontext11 : n + 11 <= n + 12)
    (Hcontext12 : n + 12 <= n + 13)
    (Hcontext13 : n + 13 <= n + 14)
    (Hcontext14 : n + 14 <= n + 15)
    (Hcontext15 : n + 15 <= n + 16)
    (Hcontext16 : n + 16 <= n + 17)
    (Hcontext17 : n + 17 <= n + 18)
    (Hcontext18 : n + 18 <= n + 19)
    (Hcontext19 : n + 19 <= n + 20)
    (Hcontext20 : n + 20 <= n + 21)
    (Hcontext21 : n + 21 <= n + 22)
    (Hcontext22 : n + 22 <= n + 23)
    (Hcontext23 : n + 23 <= n + 24)
    (Hcontext24 : n + 24 <= n + 25)
    (Hcontext25 : n + 25 <= n + 26)
    (Hcontext26 : n + 26 <= n + 27)
    (Hcontext27 : n + 27 <= n + 28)
    (Hcontext28 : n + 28 <= n + 29)
    (Hcontext29 : n + 29 <= n + 30)
    (Hcontext30 : n + 30 <= n + 31)
    (Hcontext31 : n + 31 <= n + 32)
    (Hcontext32 : n + 32 <= n + 33)
    (Hcontext33 : n + 33 <= n + 34)
    (Hcontext34 : n + 34 <= n + 35)
    (Hcontext35 : n + 35 <= n + 36)
    (Hcontext36 : n + 36 <= n + 37)
    (Hcontext37 : n + 37 <= n + 38)
    (Hcontext38 : n + 38 <= n + 39)
    (Hcontext39 : n + 39 <= n + 40)
    (Hcontext40 : n + 40 <= n + 41) :
  True.
Proof.
  assert_succeeds (idtac;
    assert (K -∗ isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) bytes -∗
      ((∃ x : bv 64, isla.ghost_state.mem_mapsto_array_def b (DfracOwn 1) bytes ∗
         ⌜bool_decide (bv_and x (BV 64 131072) = BV 64 0) = true⌝ ∗ ⌜0 <= n⌝) ∗ K))
      as Hpackage;
    [ zesu_block_base;
      try zesu_finish_package_tiers_with ltac:(package_deferring_marker);
      lazymatch goal with |- envs_entails _ _ => idtac end;
      assert_fails package_deferring_marked
    | ]).
  exact I.
Qed.

(* Positive control: the same package with the owned array and an
   unprovable fixed fact. The source route refuses the fixed fact, so the
   deferring route runs. *)
Lemma package_fixed_fact_runs_deferring `{!islaG Sigma} `{!threadG}
    (a b : Z) (bytes : list (bv 8)) (w : bv 64) (n : Z) (K : iProp Sigma)
    (Hmask : bv_and w (BV 64 131072) = BV 64 0) (Hn : 0 <= n)
    (Hcontext1 : n + 1 <= n + 2)
    (Hcontext2 : n + 2 <= n + 3)
    (Hcontext3 : n + 3 <= n + 4)
    (Hcontext4 : n + 4 <= n + 5)
    (Hcontext5 : n + 5 <= n + 6)
    (Hcontext6 : n + 6 <= n + 7)
    (Hcontext7 : n + 7 <= n + 8)
    (Hcontext8 : n + 8 <= n + 9)
    (Hcontext9 : n + 9 <= n + 10)
    (Hcontext10 : n + 10 <= n + 11)
    (Hcontext11 : n + 11 <= n + 12)
    (Hcontext12 : n + 12 <= n + 13)
    (Hcontext13 : n + 13 <= n + 14)
    (Hcontext14 : n + 14 <= n + 15)
    (Hcontext15 : n + 15 <= n + 16)
    (Hcontext16 : n + 16 <= n + 17)
    (Hcontext17 : n + 17 <= n + 18)
    (Hcontext18 : n + 18 <= n + 19)
    (Hcontext19 : n + 19 <= n + 20)
    (Hcontext20 : n + 20 <= n + 21)
    (Hcontext21 : n + 21 <= n + 22)
    (Hcontext22 : n + 22 <= n + 23)
    (Hcontext23 : n + 23 <= n + 24)
    (Hcontext24 : n + 24 <= n + 25)
    (Hcontext25 : n + 25 <= n + 26)
    (Hcontext26 : n + 26 <= n + 27)
    (Hcontext27 : n + 27 <= n + 28)
    (Hcontext28 : n + 28 <= n + 29)
    (Hcontext29 : n + 29 <= n + 30)
    (Hcontext30 : n + 30 <= n + 31)
    (Hcontext31 : n + 31 <= n + 32)
    (Hcontext32 : n + 32 <= n + 33)
    (Hcontext33 : n + 33 <= n + 34)
    (Hcontext34 : n + 34 <= n + 35)
    (Hcontext35 : n + 35 <= n + 36)
    (Hcontext36 : n + 36 <= n + 37)
    (Hcontext37 : n + 37 <= n + 38)
    (Hcontext38 : n + 38 <= n + 39)
    (Hcontext39 : n + 39 <= n + 40)
    (Hcontext40 : n + 40 <= n + 41) :
  True.
Proof.
  assert_succeeds (idtac;
    assert (K -∗ isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) bytes -∗
      ((∃ x : bv 64, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) bytes ∗
         ⌜bool_decide (bv_and x (BV 64 131072) = BV 64 0) = true⌝ ∗
         ⌜package_gate_fact n⌝) ∗ K))
      as Hpackage;
    [ zesu_block_base;
      try zesu_finish_package_tiers_with ltac:(package_deferring_marker);
      package_deferring_marked
    | ]).
  exact I.
Qed.
