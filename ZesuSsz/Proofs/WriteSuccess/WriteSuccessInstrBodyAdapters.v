Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma instr_body_wand_adapter
    `{!islaG Sigma} `{!threadG}
    (address : Z) (P Q : iProp Sigma) :
  (Q -∗ P) -∗ instr_body address P -∗ instr_body address Q.
Proof.
  rewrite instr_pre'_eq.
  iIntros "Hwand Hbody HQ".
  iApply "Hbody".
  iApply "Hwand".
  iExact "HQ".
Qed.
