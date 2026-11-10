Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A successor-style package: an existential witness that only a pure mask
   fact constrains, an owned array, and a fixed pure fact that no solver can
   prove. Shape taken from the jump of decodeItem block 697c into 698c. The
   package must not stay open because of the fixed fact: with a residual lemma
   for the fact the package closes, and without one the fact stays as its own
   pure goal. *)
Definition package_fact_aux : seal (fun n : Z => 0 <= n). Proof. by eexists. Qed.
Definition package_fact (n : Z) : Prop := package_fact_aux.(unseal) n.
Lemma package_fact_intro n : 0 <= n -> package_fact n.
Proof. unfold package_fact. rewrite package_fact_aux.(seal_eq). done. Qed.

Definition package_residual_fact_aux : seal (fun n : Z => 0 <= n). Proof. by eexists. Qed.
Definition package_residual_fact (n : Z) : Prop := package_residual_fact_aux.(unseal) n.
Lemma package_residual_fact_intro n : 0 <= n -> package_residual_fact n.
Proof.
  unfold package_residual_fact. rewrite package_residual_fact_aux.(seal_eq). done.
Qed.
#[local] Hint Resolve package_residual_fact_intro : zesu_residual.

(* Positive control: without the fixed fact the package closes. *)
Lemma package_without_fixed_fact_closes `{!islaG Sigma} `{!threadG}
    (a : Z) (bytes : list (bv 8)) (w : bv 64) (n : Z) (K : iProp Sigma)
    (Hmask : bv_and w (BV 64 131072) = BV 64 0) (Hn : 0 <= n) :
  K -∗ isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) bytes -∗
  ((∃ x : bv 64, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) bytes ∗
     ⌜bool_decide (bv_and x (BV 64 131072) = BV 64 0) = true⌝) ∗ K).
Proof. zesu_block2. Qed.

(* The residual tier closes the fixed fact inside the package. *)
Lemma package_residual_fact_closes `{!islaG Sigma} `{!threadG}
    (a : Z) (bytes : list (bv 8)) (w : bv 64) (n : Z) (K : iProp Sigma)
    (Hmask : bv_and w (BV 64 131072) = BV 64 0) (Hn : 0 <= n) :
  K -∗ isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) bytes -∗
  ((∃ x : bv 64, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) bytes ∗
     ⌜bool_decide (bv_and x (BV 64 131072) = BV 64 0) = true⌝ ∗
     ⌜package_residual_fact n⌝) ∗ K).
Proof. zesu_block2. Qed.

(* Without a residual lemma, exactly the fixed fact stays open, as a pure
   goal. The witness and the resources are committed. *)
Lemma package_fixed_fact_stays_pure `{!islaG Sigma} `{!threadG}
    (a : Z) (bytes : list (bv 8)) (w : bv 64) (n : Z) (K : iProp Sigma)
    (Hmask : bv_and w (BV 64 131072) = BV 64 0) (Hn : 0 <= n) :
  K -∗ isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) bytes -∗
  ((∃ x : bv 64, isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) bytes ∗
     ⌜bool_decide (bv_and x (BV 64 131072) = BV 64 0) = true⌝ ∗
     ⌜package_fact n⌝) ∗ K).
Proof.
  zesu_block2.
  lazymatch goal with |- package_fact n => idtac end.
  exact (package_fact_intro n Hn).
Qed.
