Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.

Set Default Proof Using "Type".

Section tests.
Context `{!islaG Sigma} `{!threadG}.

(* Two block bodies refer to each other's guarded entry contracts. *)
Lemma block_table_two_blocks (first second : Z) (P Q code : iProp Sigma) :
  □ code -∗
  □ (instr_pre second Q -∗ instr_body first P) -∗
  □ (instr_pre first P -∗ instr_body second Q) -∗
  block_table_pre {| block_table_code := code;
                     block_table_entries := [(first, P); (second, Q)] |}.
Proof.
  iIntros "#Hcode #Hfirst #Hsecond".
  iApply (block_table_complete
    {| block_table_code := code;
       block_table_entries := [(first, P); (second, Q)] |}
    with "Hcode"). iModIntro.
  iIntros (address state) "%Hentry #Htable".
  iEval (rewrite /block_table_pre /=) in "Htable".
  iDestruct "Htable" as "[_ [HfirstPre [HsecondPre _]]]".
  rewrite !elem_of_cons elem_of_nil in Hentry.
  destruct Hentry as [Heq | [Heq | []]].
  - inversion Heq; subst. iApply ("Hfirst" with "HsecondPre").
  - inversion Heq; subst. iApply ("Hsecond" with "HfirstPre").
Qed.

Lemma block_table_two_bodies (first second : Z) (P Q code : iProp Sigma) :
  □ code -∗
  □ (instr_pre second Q -∗ instr_body first P) -∗
  □ (instr_pre first P -∗ instr_body second Q) -∗
  instr_body first P ∗ instr_body second Q.
Proof.
  iIntros "#Hcode #Hfirst #Hsecond".
  iPoseProof (block_table_two_blocks with "Hcode Hfirst Hsecond") as "#Htable".
  iEval (rewrite /block_table_pre /=) in "Htable".
  iDestruct "Htable" as "[_ [HfirstPre [HsecondPre _]]]".
  iSplitL "".
  - iApply ("Hfirst" with "HsecondPre").
  - iApply ("Hsecond" with "HfirstPre").
Qed.

(* A successor continuation accepts the selected entry parameter. *)
Lemma block_table_selected_continuation {A : Type} (pc : Z)
    (state : A -> iProp Sigma) (selected : A) :
  instr_pre pc (∃ parameter, state parameter)%I -∗ instr_pre pc (state selected).
Proof.
  rewrite instr_pre_existential_instantiation.
  iIntros "Hnext". iApply ("Hnext" $! selected).
Qed.

(* The table body eliminates its entry witness through the native family. *)
Lemma block_table_existential_body {A : Type} (pc : Z)
    (state : A -> iProp Sigma) :
  (∀ parameter, instr_body pc (state parameter)) -∗
    instr_body pc (∃ parameter, state parameter)%I.
Proof.
  rewrite instr_pre_existential_instantiation.
  iIntros "Hbody". iExact "Hbody".
Qed.

End tests.
Print Assumptions block_table_two_blocks.
Print Assumptions block_table_two_bodies.
Print Assumptions block_table_selected_continuation.
Print Assumptions block_table_existential_body.
