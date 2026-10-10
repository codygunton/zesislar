Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Contracts.DecodeItemSelected.

Section complete_family.
Context `{!islaG Sigma} `{!threadG}.
Context (pending800d6960 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6960 decodeItemState800d6960).
Context (pending800d6974 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6974 decodeItemState800d6974).
Context (pending800d697c :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d697c decodeItemState800d697c).
Context (pending800d698c :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d698c decodeItemState800d698c).
Context (pending800d69b0 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69b0 decodeItemState800d69b0).
Context (pending800d69e8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69e8 decodeItemState800d69e8).
Context (pending800d6a08 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a08 decodeItemState800d6a08).
Context (pending800d6a24 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a24 decodeItemState800d6a24).
Context (pending800d6a38 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a38 decodeItemState800d6a38).
Context (pending800d6a40 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a40 decodeItemState800d6a40).
Context (pending800d6a78 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a78 decodeItemState800d6a78).
Context (pending800d6aa8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6aa8 decodeItemState800d6aa8).
Context (pending800d6ac4 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ac4 decodeItemState800d6ac4).
Context (pending800d6ad8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ad8 decodeItemState800d6ad8).
Context (pending800d6ae0 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ae0 decodeItemState800d6ae0).
Context (pending800d6b08 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6b08 decodeItemState800d6b08).

(* All table members use their exact existential entry family. *)
Lemma decodeItemBlockTable_body_family :
  ⊢ □ (∀ address state, ⌜(address, state) ∈ block_table_entries decodeItemBlockTable⌝ -∗
    block_table_pre decodeItemBlockTable -∗ instr_body address state).
Proof using H Sigma islaG0
  pending800d6960 pending800d6974 pending800d697c pending800d698c pending800d69b0 pending800d69e8 pending800d6a08 pending800d6a24
  pending800d6a38 pending800d6a40 pending800d6a78 pending800d6aa8 pending800d6ac4 pending800d6ad8 pending800d6ae0 pending800d6b08.
  iModIntro. iIntros (address state) "%Hentry #Htable".
  change ((address, state) ∈ block_table_entries decodeItemBlockTable) in Hentry.
  rewrite /decodeItemBlockTable /= !elem_of_cons elem_of_nil in Hentry.
  destruct Hentry as [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | [Heq | []]]]]]]]]]]]]]]]]]]]]]]]].
  - inversion Heq; subst. iApply (pending800d6960 with "Htable").
  - inversion Heq; subst. iApply (pending800d6974 with "Htable").
  - inversion Heq; subst. iApply (pending800d697c with "Htable").
  - inversion Heq; subst. iApply (pending800d698c with "Htable").
  - inversion Heq; subst. iApply (decodeItemPromotedBody800d69a4 with "Htable").
  - inversion Heq; subst. iApply (pending800d69b0 with "Htable").
  - inversion Heq; subst. iApply (decodeItemPromotedBody800d69d8 with "Htable").
  - inversion Heq; subst. iApply (decodeItemPromotedBody800d69e0 with "Htable").
  - inversion Heq; subst. iApply (pending800d69e8 with "Htable").
  - inversion Heq; subst. iApply (decodeItemPromotedBody800d6a00 with "Htable").
  - inversion Heq; subst. iApply (pending800d6a08 with "Htable").
  - inversion Heq; subst. iApply (decodeItemPromotedBody800d6a14 with "Htable").
  - inversion Heq; subst. iApply (pending800d6a24 with "Htable").
  - inversion Heq; subst. iApply (pending800d6a38 with "Htable").
  - inversion Heq; subst. iApply (pending800d6a40 with "Htable").
  - inversion Heq; subst. iApply (decodeItemPromotedBody800d6a64 with "Htable").
  - inversion Heq; subst. iApply (decodeItemPromotedBody800d6a6c with "Htable").
  - inversion Heq; subst. iApply (pending800d6a78 with "Htable").
  - inversion Heq; subst. iApply (pending800d6aa8 with "Htable").
  - inversion Heq; subst. iApply (decodeItemPromotedBody800d6ab4 with "Htable").
  - inversion Heq; subst. iApply (pending800d6ac4 with "Htable").
  - inversion Heq; subst. iApply (pending800d6ad8 with "Htable").
  - inversion Heq; subst. iApply (pending800d6ae0 with "Htable").
  - inversion Heq; subst. iApply (pending800d6b08 with "Htable").
Qed.

(* Supply the pending slot theorems and boxed code in one application. *)
Lemma decodeItemBlockTable_complete_family :
  □ decodeItemSelectedCode -∗ block_table_pre decodeItemBlockTable.
Proof using H Sigma islaG0
  pending800d6960 pending800d6974 pending800d697c pending800d698c pending800d69b0 pending800d69e8 pending800d6a08 pending800d6a24
  pending800d6a38 pending800d6a40 pending800d6a78 pending800d6aa8 pending800d6ac4 pending800d6ad8 pending800d6ae0 pending800d6b08.
  iIntros "#Hcode".
  iApply (block_table_complete decodeItemBlockTable with "Hcode []").
  iApply decodeItemBlockTable_body_family.
Qed.
End complete_family.

Print Assumptions decodeItemBlockTable_body_family.
Print Assumptions decodeItemBlockTable_complete_family.
