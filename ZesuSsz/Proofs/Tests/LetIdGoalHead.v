From Coq Require Import ZArith.ZArith Lists.List.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Section let_id_goal.
  Context `{!islaG Sigma}.

  (* A pass end left the let-bound continuation as `LET_ID T args` under the
     lazy existential. Lithium's own steps stop there; after the step,
     Lithium goes on and sets the existential. *)
  Goal forall (bytes : list (bv 8)) (R : list (bv 8) -> iProp Sigma),
    R bytes ⊢ ∃ (other : bv 64) (list_value : list (bv 8)),
      LET_ID (fun value : list (bv 8) => ⌜value = bytes⌝ ∗ R value)%I list_value.
  Proof.
    intros bytes R. iStartProof. iIntros "HR".
    repeat liExist.
    Fail liStep.
    zesu_unfold_let_id_goal.
    liSideCond.
    lazymatch goal with |- environments.envs_entails _ (∃ _ : unit, R bytes) => idtac end.
    iExists tt. iExact "HR".
  Qed.

  (* No wrapper in the goal: no step. *)
  Goal forall (bytes : list (bv 8)) (R : list (bv 8) -> iProp Sigma), R bytes ⊢ R bytes.
  Proof.
    intros bytes R. iStartProof. iIntros "HR".
    Fail zesu_unfold_let_id_goal.
    iExact "HR".
  Qed.
End let_id_goal.
