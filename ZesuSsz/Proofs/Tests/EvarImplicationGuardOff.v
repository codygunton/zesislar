Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Lemma unresolved_implication_off (length : nat) : True.
Proof.
  let index := open_constr:(_ : nat) in
  assert (Hprobe : (index < length)%nat -> True);
  [ liImpl; constr_eq index (0%nat); intros _; exact I | exact I ].
Qed.
Print Assumptions unresolved_implication_off.
