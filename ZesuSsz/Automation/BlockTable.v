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

(* Fold proved bodies into the table interface without comparing states. *)
Lemma block_table_cases_from_bodies (table : blockTable Sigma) :
  ([∗ list] entry ∈ block_table_entries table, instr_body entry.1 entry.2) -∗
  ∀ address state, ⌜(address, state) ∈ block_table_entries table⌝ -∗ instr_body address state.
Proof.
  iIntros "Hbodies" (address state Hentry).
  iApply (big_sepL_elem_of _ _ (address, state) with "Hbodies"). exact Hentry.
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

(* Every native witness must support every table binder. *)
Lemma successor_state_support_from_each {A B : Type}
    (native : A -> iProp Sigma) (universal : B -> iProp Sigma) :
  (forall native_witness table_binder,
     native native_witness ⊢ universal table_binder) ->
  (∃ native_witness, native native_witness) ⊢
    ∀ table_binder, universal table_binder.
Proof.
  intros Hsupport. iIntros "[%witness Hnative]" (binder).
  iApply (Hsupport witness binder with "Hnative").
Qed.

(* Continuations require the state entailment in the reverse direction. *)
Lemma instr_pre_successor_support {A B : Type} (pc : Z)
    (native : A -> iProp Sigma) (universal : B -> iProp Sigma) :
  ((∃ native_witness, native native_witness) ⊢
     ∀ table_binder, universal table_binder) ->
  instr_pre pc (∀ table_binder, universal table_binder) -∗
  instr_pre pc (∃ native_witness, native native_witness).
Proof.
  intros Hsupport. iIntros "Huniversal".
  iApply (instr_pre_wand with "Huniversal []"); [done|done|].
  iIntros "Hnative". iApply (Hsupport with "Hnative").
Qed.

End block_table.
Print Assumptions block_table_pre_code.
Print Assumptions block_table_pre_lookup.
Print Assumptions block_table_complete.
Print Assumptions block_table_body.
Print Assumptions successor_state_support_from_each.
Print Assumptions instr_pre_successor_support.
