Require Import isla.riscv64.riscv64.

Lemma instr_body_exists `{!islaG Sigma} `{!threadG} {A : Type}
    (pc : Z) (P : A -> iProp Sigma) :
  (∀ argument, instr_body pc (P argument)) -∗
  instr_body pc (∃ argument, P argument).
Proof.
  rewrite instr_pre'_eq /instr_pre'_def.
  iIntros "Hbody Hargument".
  iDestruct "Hargument" as (argument) "Hargument".
  iApply ("Hbody" $! argument with "Hargument").
Qed.
Print Assumptions instr_body_exists.
