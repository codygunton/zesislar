Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.EntryIntro.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSavedFrameWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemInputHeadWordFacts.
Open Scope Z_scope.

Lemma route_a_entry_equality `{!islaG Sigma} `{!threadG} returnAddress args :
 ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6960 returnAddress args ⊢
 ⌜decodeItemReturnAddress args = returnAddress /\
   (bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0 ->
    decodeItemInputHead args (List.hd (0%bv) (decodeItemInputBytes args))
      (List.tl (decodeItemInputBytes args)))⌝.
Proof.
 rewrite /ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6960 /decodeItemEntryResources.
 iIntros "[Hentry _]".
 iDestruct "Hentry" as (a3 a4 a5 a6) "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hd & _)".
 iPureIntro. split.
 - exact (proj1 Hd).
 - intros Hnonzero.
   destruct (decodeItemDomainNonemptyInputHead returnAddress args Hd Hnonzero)
     as (prefix & rest & Hhead).
   unfold decodeItemInputHead in *. rewrite Hhead. reflexivity.
Qed.
#[export] Instance decodeItemCanonicalHeadEntryIntro
 `{!islaG Sigma} `{!threadG} returnAddress args :
 ZesuEntryIntro (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6960 returnAddress args)
 (decodeItemReturnAddress args = returnAddress /\
   (bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0 ->
    decodeItemInputHead args (List.hd (0%bv) (decodeItemInputBytes args))
      (List.tl (decodeItemInputBytes args)))) :=
 route_a_entry_equality returnAddress args.
#[export] Instance input_length_word_nonzero_derived args :
 ZesuDerivedFacts (Z_to_bv 64 (decodeItemInputLength args) <> 0%bv)
 (bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0) :=
 decodeItemInputLengthWordNonzero args.

#[export] Hint Extern 1 (SimplAnd (decodeItemSavedFrameFacts ?args ?bytes) True) =>
 assert_fails (has_evar bytes);
 match goal with
 | Hdomain : decodeItemDomainAt ?ra decodeItemC1BDomain args |- _ =>
   unfold SimplAnd; split;
   [intros _; exact (decodeItemSavedFrameFacts_machine_words args (proj2 Hdomain))
   |intros _; exact I]
 end : typeclass_instances.
#[export] Hint Extern 1 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
 match goal with
 | Hdomain : decodeItemDomainAt ?ra decodeItemC1BDomain args,
   Hzero : Z_to_bv 64 (decodeItemInputLength args) = 0%bv |- _ =>
   unfold SimplAnd; split;
   [intros _; exact (decodeItemSavedFrameZeroRejected ra args Hdomain Hzero)
   |intros _; exact I]
 end : typeclass_instances.
