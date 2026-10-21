Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Record blockTable (Sigma : gFunctors) := {
  block_table_code : iProp Sigma;
  block_table_entries : list (Z * iProp Sigma);
}.
Arguments block_table_code {_} _.
Arguments block_table_entries {_} _.

Section block_table.
Context `{!islaG Sigma} `{!threadG}.

Definition block_table_pre (table : blockTable Sigma) : iProp Sigma :=
  (□ block_table_code table ∗
   [∗ list] entry ∈ block_table_entries table, □ instr_pre entry.1 entry.2)%I.

Lemma block_table_pre_code (table : blockTable Sigma) :
  block_table_pre table -∗ □ block_table_code table.
Proof. iIntros "[$ _]". Qed.

Lemma block_table_pre_lookup (table : blockTable Sigma) address state :
  (address, state) ∈ block_table_entries table ->
  block_table_pre table -∗ □ instr_pre address state.
Proof.
  intros Hentry. rewrite /block_table_pre.
  iIntros "[_ Htable]".
  iApply (big_sepL_elem_of _ _ (address, state) with "Htable"). exact Hentry.
Qed.

(* Each block starts without a later. Successor contracts carry the guard. *)
Lemma block_table_complete (table : blockTable Sigma) :
  □ block_table_code table -∗
  □ (∀ address state, ⌜(address, state) ∈ block_table_entries table⌝ -∗
      block_table_pre table -∗ instr_body address state) -∗
  block_table_pre table.
Proof.
  iIntros "#Hcode #Hblocks". iLöb as "IH".
  rewrite /block_table_pre. iSplit; first iExact "Hcode".
  iApply big_sepL_intro.
  iIntros "!>" (index [address state] Hentry).
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply ("Hblocks" $! address state with "[] IH").
  iPureIntro. apply elem_of_list_lookup_2 with index. exact Hentry.
Qed.

Lemma block_table_body (table : blockTable Sigma) address state :
  (address, state) ∈ block_table_entries table ->
  □ block_table_code table -∗
  □ (∀ address state, ⌜(address, state) ∈ block_table_entries table⌝ -∗
      block_table_pre table -∗ instr_body address state) -∗
  instr_body address state.
Proof.
  intros Hentry. iIntros "#Hcode #Hblocks".
  iPoseProof (block_table_complete with "Hcode Hblocks") as "Htable".
  iApply ("Hblocks" $! address state with "[] Htable"). done.
Qed.

(* Consume the selected witness with its matching continuation. *)
Lemma successor_state_existential_consume {A : Type}
    (P : A -> iProp Sigma) (Q : iProp Sigma) :
  ((∃ witness, P witness) ∗ (∀ parameter, P parameter -∗ Q))%I ⊢ Q.
Proof.
  iIntros "[[%witness HP] Hnext]".
  iApply ("Hnext" $! witness with "HP").
Qed.

(* Quantify entry parameters outside the instruction precondition. *)
Lemma instr_pre_existential_instantiation {A : Type}
    (guarded : bool) (pc : Z) (state : A -> iProp Sigma) :
  instr_pre' guarded pc (∃ witness, state witness)%I ⊣⊢
    (∀ parameter, instr_pre' guarded pc (state parameter))%I.
Proof.
  destruct guarded;
    rewrite !instr_pre'_eq /instr_pre'_def /= bi.exist_wand_forall;
    [rewrite bi.later_forall |]; done.
Qed.

End block_table.
Print Assumptions block_table_pre_code.
Print Assumptions block_table_pre_lookup.
Print Assumptions block_table_complete.
Print Assumptions block_table_body.
Print Assumptions successor_state_existential_consume.
Print Assumptions instr_pre_existential_instantiation.
