Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Definition blockTable (Sigma : gFunctors) := list (Z * iProp Sigma).

Section block_table.
Context `{!islaG Sigma} `{!threadG}.

Definition block_table_pre (table : blockTable Sigma) : iProp Sigma :=
  ([∗ list] entry ∈ table, □ instr_pre entry.1 entry.2)%I.

Lemma block_table_pre_lookup (table : blockTable Sigma) address state :
  (address, state) ∈ table ->
  block_table_pre table -∗ □ instr_pre address state.
Proof.
  intros Hentry. rewrite /block_table_pre.
  iIntros "Htable".
  iApply (big_sepL_elem_of _ _ (address, state) with "Htable"). exact Hentry.
Qed.

(* Each block starts without a later. Successor contracts carry the guard. *)
Lemma block_table_complete (table : blockTable Sigma) :
  □ (∀ address state, ⌜(address, state) ∈ table⌝ -∗
      block_table_pre table -∗ instr_body address state) -∗
  block_table_pre table.
Proof.
  iIntros "#Hblocks". iLöb as "IH".
  rewrite /block_table_pre. iApply big_sepL_intro.
  iIntros "!>" (index [address state] Hentry).
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply ("Hblocks" $! address state with "[] IH").
  iPureIntro. apply elem_of_list_lookup_2 with index. exact Hentry.
Qed.

Lemma block_table_body (table : blockTable Sigma) address state :
  (address, state) ∈ table ->
  □ (∀ address state, ⌜(address, state) ∈ table⌝ -∗
      block_table_pre table -∗ instr_body address state) -∗
  instr_body address state.
Proof.
  intros Hentry. iIntros "#Hblocks".
  iPoseProof (block_table_complete with "Hblocks") as "Htable".
  iApply ("Hblocks" $! address state with "[] Htable"). done.
Qed.

End block_table.
Print Assumptions block_table_pre_lookup.
Print Assumptions block_table_complete.
Print Assumptions block_table_body.
