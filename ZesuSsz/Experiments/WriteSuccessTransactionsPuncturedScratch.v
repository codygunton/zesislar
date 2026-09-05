From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsPuncturedScratch `{!islaG Sigma}
    (sp : bv 64) (base : Z) (total : nat) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ? 984 ∗
   (bv_unsigned sp + 1136) ↦ₘ? 760 ∗ True)%I.

Definition writeSuccessTransactionsWordsCarrier `{!islaG Sigma}
    (sp first second third fourth : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 1104) ↦ₘ first ∗
   (bv_unsigned sp + 1112) ↦ₘ second ∗
   (bv_unsigned sp + 1120) ↦ₘ third ∗
   (bv_unsigned sp + 1128) ↦ₘ fourth)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPuncturedScratch) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWordsCarrier) := I.

Lemma write_success_transactions_scratch_split_carrier
    `{!islaG Sigma} (sp : bv 64) (base : Z) (total : nat) :
  writeSuccessTransactionsScratch sp base total -∗
  ∃ first second third fourth,
    writeSuccessTransactionsPuncturedScratch sp base total ∗
    writeSuccessTransactionsWordsCarrier sp first second third fourth.
Proof.
  iIntros "Hscratch".
  iEval (unfold writeSuccessTransactionsScratch) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower & Hbase & Htotal & Hupper & _)".
  iDestruct (mem_mapsto_uninit_split 984 with "Hupper") as
    "[Hprefix Hrest]"; first lia.
  have HfirstAddress : bv_unsigned sp + 120 + 984 =
      bv_unsigned sp + 1104 by lia.
  iEval (rewrite HfirstAddress) in "Hrest".
  iDestruct (mem_mapsto_uninit_split 8 with "Hrest") as
    "[Hfirst Hrest]"; first lia.
  have HsecondAddress : bv_unsigned sp + 1104 + 8 =
      bv_unsigned sp + 1112 by lia.
  iEval (rewrite HsecondAddress) in "Hrest".
  iDestruct (mem_mapsto_uninit_split 8 with "Hrest") as
    "[Hsecond Hrest]"; first lia.
  have HthirdAddress : bv_unsigned sp + 1112 + 8 =
      bv_unsigned sp + 1120 by lia.
  iEval (rewrite HthirdAddress) in "Hrest".
  iDestruct (mem_mapsto_uninit_split 8 with "Hrest") as
    "[Hthird Hrest]"; first lia.
  have HfourthAddress : bv_unsigned sp + 1120 + 8 =
      bv_unsigned sp + 1128 by lia.
  iEval (rewrite HfourthAddress) in "Hrest".
  iDestruct (mem_mapsto_uninit_split 8 with "Hrest") as
    "[Hfourth Hsuffix]"; first lia.
  have HsuffixAddress : bv_unsigned sp + 1128 + 8 =
      bv_unsigned sp + 1136 by lia.
  iEval (rewrite HsuffixAddress;
    replace (1776 - 984 - 8 - 8 - 8 - 8)%Z with 760%Z by lia) in "Hsuffix".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hfirst") as
    (firstLength first HfirstLength) "Hfirst".
  cbn in HfirstLength. subst firstLength.
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hsecond") as
    (secondLength second HsecondLength) "Hsecond".
  cbn in HsecondLength. subst secondLength.
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hthird") as
    (thirdLength third HthirdLength) "Hthird".
  cbn in HthirdLength. subst thirdLength.
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hfourth") as
    (fourthLength fourth HfourthLength) "Hfourth".
  cbn in HfourthLength. subst fourthLength.
  iExists first, second, third, fourth.
  rewrite /writeSuccessTransactionsPuncturedScratch
    /writeSuccessTransactionsWordsCarrier.
  iFrame.
Qed.

Lemma write_success_transactions_scratch_combine_carrier
    `{!islaG Sigma} (sp first second third fourth : bv 64)
    (base : Z) (total : nat) :
  writeSuccessTransactionsPuncturedScratch sp base total -∗
  writeSuccessTransactionsWordsCarrier sp first second third fourth -∗
  writeSuccessTransactionsScratch sp base total.
Proof.
  iIntros "Hscratch Hcarrier".
  iEval (unfold writeSuccessTransactionsPuncturedScratch) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower & Hbase & Htotal & Hprefix & Hsuffix & _)".
  iEval (unfold writeSuccessTransactionsWordsCarrier) in "Hcarrier".
  iDestruct "Hcarrier" as "(Hfirst & Hsecond & Hthird & Hfourth)".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "Hfirst") as "Hfirst".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "Hsecond") as "Hsecond".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "Hthird") as "Hthird".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "Hfourth") as "Hfourth".
  iAssert ((bv_unsigned sp + 1104) ↦ₘ? 32)%I
    with "[Hfirst Hsecond Hthird Hfourth]" as "Hwords".
  { iApply (mem_mapsto_uninit_combine 8 with "Hfirst"); first lia.
    have -> : bv_unsigned sp + 1104 + 8 = bv_unsigned sp + 1112 by lia.
    iApply (mem_mapsto_uninit_combine 8 with "Hsecond"); first lia.
    have -> : bv_unsigned sp + 1112 + 8 = bv_unsigned sp + 1120 by lia.
    iApply (mem_mapsto_uninit_combine 8 with "Hthird"); first lia.
    have -> : bv_unsigned sp + 1120 + 8 = bv_unsigned sp + 1128 by lia.
    iExact "Hfourth". }
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 1776)%I
    with "[Hprefix Hwords Hsuffix]" as "Hupper".
  { iApply (mem_mapsto_uninit_combine 984 with "Hprefix"); first lia.
    have -> : bv_unsigned sp + 120 + 984 = bv_unsigned sp + 1104 by lia.
    iApply (mem_mapsto_uninit_combine 32 with "Hwords"); first lia.
    have -> : bv_unsigned sp + 1104 + 32 = bv_unsigned sp + 1136 by lia.
    iExact "Hsuffix". }
  rewrite /writeSuccessTransactionsScratch.
  iFrame.
Qed.
