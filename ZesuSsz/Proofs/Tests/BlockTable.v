Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.

Section tests.
Context `{!islaG Sigma} `{!threadG}.

(* Two block bodies refer to each other's guarded entry contracts. *)
Lemma block_table_two_blocks (first second : Z) (P Q : iProp Sigma) :
  □ (instr_pre second Q -∗ instr_body first P) -∗
  □ (instr_pre first P -∗ instr_body second Q) -∗
  block_table_pre [(first, P); (second, Q)].
Proof.
  iIntros "#Hfirst #Hsecond". iApply block_table_complete. iModIntro.
  iIntros (address state) "%Hentry #Htable".
  iEval (rewrite /block_table_pre /=) in "Htable".
  iDestruct "Htable" as "[HfirstPre [HsecondPre _]]".
  rewrite !elem_of_cons elem_of_nil in Hentry.
  destruct Hentry as [Heq | [Heq | []]].
  - inversion Heq; subst. iApply ("Hfirst" with "HsecondPre").
  - inversion Heq; subst. iApply ("Hsecond" with "HfirstPre").
Qed.

Lemma block_table_two_bodies (first second : Z) (P Q : iProp Sigma) :
  □ (instr_pre second Q -∗ instr_body first P) -∗
  □ (instr_pre first P -∗ instr_body second Q) -∗
  instr_body first P ∗ instr_body second Q.
Proof.
  iIntros "#Hfirst #Hsecond".
  iPoseProof (block_table_two_blocks with "Hfirst Hsecond") as "#Htable".
  iEval (rewrite /block_table_pre /=) in "Htable".
  iDestruct "Htable" as "[HfirstPre [HsecondPre _]]".
  iSplitL "".
  - iApply ("Hfirst" with "HsecondPre").
  - iApply ("Hsecond" with "HfirstPre").
Qed.

End tests.
Print Assumptions block_table_two_blocks.
Print Assumptions block_table_two_bodies.
