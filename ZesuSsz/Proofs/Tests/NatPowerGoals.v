Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.NatPowerGoals.

Lemma test_large_nat_bound_goal {Sigma : gFunctors} (count : nat) :
  (count < 2 ^ 64)%nat ->
  (Z.of_nat count < 2 ^ 64)%Z ->
  (True : iProp Sigma) ⊢ ⌜(count < 2 ^ 64)%nat⌝ ∗ True.
Proof.
  intros Hnatural Hcount. iStartProof. iIntros "_".
  cbn [Nat.pow]. zesu_run_nat_safe.
Qed.
Print Assumptions test_large_nat_bound_goal.
