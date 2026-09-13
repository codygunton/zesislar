Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Continuations.
Require Import isla.riscv64.riscv64.

Lemma false_body_unreachable `{!islaG Sigma} `{!threadG} pc (P : iProp Sigma) :
  (P -∗ False) -∗ instr_body pc P.
Proof.
  iIntros "Hfalse".
  iPoseProof (instr_body_false pc) as "Hbody".
  iApply (instr_pre_wand pc pc false false with "Hbody"); [done | reflexivity |].
  iExact "Hfalse".
Qed.
Print Assumptions false_body_unreachable.
