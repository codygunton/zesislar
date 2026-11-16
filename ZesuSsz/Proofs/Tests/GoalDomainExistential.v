Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.

(* The goal domain step (Automation2/GoalDomain.v) refuses an existential
   before it unfolds or simplifies anything. Here a registered head under the
   binder lets the step open the goal, and its `cbn` would then run
   `parity_probe` over 10^8 in unary; the earlier step did not finish. *)
Fixpoint parity_probe (n : nat) : bool :=
  match n with O => true | S k => negb (parity_probe k) end.
Definition existential_domain_probe (b : bool) : Prop :=
  b = parity_probe (Nat.pow 10 8).
#[local] Hint Unfold existential_domain_probe : zesu_goal_domain.

Lemma goal_domain_refuses_existential : True.
Proof.
  Fail assert (exists b, existential_domain_probe b)
    by ZesuSsz.Automation2.GoalDomain.zesu_finish_goal_domain.
  exact I.
Qed.
