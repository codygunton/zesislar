Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.EvarImplicationGuard.

Lemma unresolved_implication_guard (length : nat) : True.
Proof.
  let index := open_constr:(_ : nat) in
  assert (Hprobe : (index < length)%nat -> True);
  [ assert_fails liImpl; has_evar index; unify index 1%nat; intro; exact I | exact I ].
Qed.

Lemma alias_implication_guard (length : nat) : True.
Proof.
  let index := open_constr:(_ : nat) in
  let alias := fresh "alias" in pose (alias := index);
  assert (Hprobe : (alias < length)%nat -> True);
  [ assert_fails liImpl; has_evar index; unify index 1%nat; intro; exact I | exact I ].
Qed.

Lemma fixed_implication_guard (length : nat) : (0 < length)%nat -> True.
Proof. liImpl. intros _. exact I. Qed.
Print Assumptions unresolved_implication_guard.
Print Assumptions alias_implication_guard.
Print Assumptions fixed_implication_guard.
