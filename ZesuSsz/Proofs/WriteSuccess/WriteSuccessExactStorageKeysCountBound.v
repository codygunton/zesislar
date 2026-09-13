Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Lemma storage_keys_count_bound remaining :
  (S remaining < 2 ^ 64)%nat ->
  Z.of_nat remaining < 18446744073709551616.
Proof.
  intros Hcount. apply Nat2Z.inj_lt in Hcount.
  rewrite Nat2Z.inj_pow Nat2Z.inj_succ in Hcount.
  change (Z.succ (Z.of_nat remaining) < 18446744073709551616) in Hcount.
  lia.
Qed.
Print Assumptions storage_keys_count_bound.
