Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A defined fact that no solver interprets. Shape taken from the semantic
   successor fact of decodeItem block 69e8 (a candidate decoder result plus a
   Sail run): lia and bv_solve see it as an opaque atom and could close it
   only by refuting every fact in the context. The finisher leaves such a
   goal to the shape-specific closers and the residual tier. The
   contradictory context below makes the refusal visible: a whole-context
   refutation would close the goal. *)
Definition solver_opaque_fact_aux : seal (fun n : Z => 0 <= n). Proof. by eexists. Qed.
Definition solver_opaque_fact (n : Z) : Prop := solver_opaque_fact_aux.(unseal) n.

Lemma finisher_refuses_opaque_goal (n : Z) (Hlow : 5 < n) (Hhigh : n < 3) :
  solver_opaque_fact n.
Proof.
  try ZesuSsz.Automation2.BoundedArithmetic.zesu_finish_lia.
  try zesu_finish_pure_goal_base.
  try zesu_finish_v1.
  lazymatch goal with |- solver_opaque_fact n => idtac end.
  exfalso; lia.
Qed.

(* An equation between lists is not a solver goal either. *)
Lemma finisher_refuses_list_equation (n : Z) (xs : list Z) (Hlow : 5 < n) (Hhigh : n < 3) :
  xs = [n].
Proof.
  try ZesuSsz.Automation2.BoundedArithmetic.zesu_finish_lia.
  lazymatch goal with |- xs = [n] => idtac end.
  exfalso; lia.
Qed.

(* Positive controls: the finisher still proves arithmetic goals, explicit
   refutations, and arithmetic under connectives. A proof outside the
   finisher can still refute a context with lia. *)
Lemma finisher_keeps_arithmetic_goal (n : Z) (Hlow : 5 < n) : 3 < n /\ n <> 2.
Proof. ZesuSsz.Automation2.BoundedArithmetic.zesu_finish_lia. Qed.

Lemma finisher_keeps_refutation (n : Z) (Hlow : 5 < n) (Hhigh : n < 3) : False.
Proof. ZesuSsz.Automation2.BoundedArithmetic.zesu_finish_lia. Qed.

Lemma finisher_keeps_implication (n m : nat) : (n < m)%nat -> (n <= m)%nat.
Proof. ZesuSsz.Automation2.BoundedArithmetic.zesu_finish_lia. Qed.

Lemma plain_lia_keeps_refutation (n : Z) (Hlow : 5 < n) (Hhigh : n < 3) :
  solver_opaque_fact n.
Proof. lia. Qed.
