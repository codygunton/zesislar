From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessValueTransactionsEntry.

Import ListNotations.

(** This handoff separates the four decoded value words from the broad value
    scratch.  The list equation is discharged by the value-block proof. *)
Lemma write_success_value_transactions_carrier_handoff
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat)
    (values : list (bv 64)) (first second third fourth : bv 64)
    (items : list ByteListItem)
    (HvaluesLength : length values = 74%nat)
    (Hfacts : writeSuccessTransactionsPost15674ByteListFacts
      sp first second items) :
  (bv_unsigned sp - 48) ↦ₘ? 48 -∗
  (bv_unsigned sp - 80) ↦ₘ? 32 -∗
  bv_unsigned sp ↦ₘ? 104 -∗
  (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base -∗
  (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) -∗
  (bv_unsigned sp + 120) ↦ₘ? 912 -∗
  (bv_unsigned sp + 1032) ↦ₘ∗
    (take 9 values ++ [first; second; third; fourth] ++ drop 13 values) -∗
  (bv_unsigned sp + 1624) ↦ₘ? 272 -∗
  byteListItemResources (bv_unsigned first) items -∗
  writeSuccessTransactionsPuncturedScratch sp base total ∗
  writeSuccessTransactionsLoopCarrierPayload
    sp first second third fourth items ∗
  (bv_unsigned sp + 1744) ↦ₘ? 48.
Proof.
  iIntros "Hlower Hcall Hgap104 Hbase Htotal Hgap Hvalues Htail Hitems".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower Hgap104]" as "Hlower".
  { iApply (mem_mapsto_uninit_combine 48 with "Hlower"); first lia.
    replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by lia.
    iExact "Hgap104". }
  set prefix := take 9 values.
  set suffix := drop 13 values.
  iDestruct (mem_mapsto_array_app 64%N (bv_unsigned sp + 1032)
    (DfracOwn 1) prefix
    ([first; second; third; fourth] ++ suffix)
    with "Hvalues") as "[Hprefix Hrest]".
  have HprefixLength : length prefix = 9%nat.
  { cbn [prefix]. rewrite length_take HvaluesLength. lia. }
  have HrestAddress :
      bv_unsigned sp + 1032 + Z.of_N (64 `div` 8) * 9%nat =
      bv_unsigned sp + 1104 by cbn; lia.
  iEval (rewrite HprefixLength HrestAddress) in "Hrest".
  iDestruct (mem_mapsto_array_app 64%N (bv_unsigned sp + 1104)
    (DfracOwn 1) [first; second; third; fourth] suffix
    with "Hrest") as "[Hwords HvaluesRest]".
  iDestruct (mem_mapsto_array_app 64%N (bv_unsigned sp + 1104)
    (DfracOwn 1) [first] [second; third; fourth] with "Hwords") as
    "[Hfirst Hwords]".
  iDestruct (mem_mapsto_array_singleton with "Hfirst") as "Hfirst".
  have HsecondAddress :
      bv_unsigned sp + 1104 + Z.of_N (64 `div` 8) * 1%nat =
      bv_unsigned sp + 1112 by cbn; lia.
  iEval (rewrite HsecondAddress) in "Hwords".
  iDestruct (mem_mapsto_array_app 64%N (bv_unsigned sp + 1112)
    (DfracOwn 1) [second] [third; fourth] with "Hwords") as
    "[Hsecond Hwords]".
  iDestruct (mem_mapsto_array_singleton with "Hsecond") as "Hsecond".
  have HthirdAddress :
      bv_unsigned sp + 1112 + Z.of_N (64 `div` 8) * 1%nat =
      bv_unsigned sp + 1120 by cbn; lia.
  iEval (rewrite HthirdAddress) in "Hwords".
  iDestruct (mem_mapsto_array_app 64%N (bv_unsigned sp + 1120)
    (DfracOwn 1) [third] [fourth] with "Hwords") as
    "[Hthird Hfourth]".
  iDestruct (mem_mapsto_array_singleton with "Hthird") as "Hthird".
  have HfourthAddress :
      bv_unsigned sp + 1120 + Z.of_N (64 `div` 8) * 1%nat =
      bv_unsigned sp + 1128 by cbn; lia.
  iEval (rewrite HfourthAddress) in "Hfourth".
  iDestruct (mem_mapsto_array_singleton with "Hfourth") as "Hfourth".
  have HsuffixAddress :
      bv_unsigned sp + 1104 + Z.of_N (64 `div` 8) * 4%nat =
      bv_unsigned sp + 1136 by cbn; lia.
  iEval (rewrite HsuffixAddress) in "HvaluesRest".
  iPoseProof (write_success_u64_array_to_uninit
    (bv_unsigned sp + 1032) prefix with "Hprefix") as
    "Hprefix".
  iEval (rewrite HprefixLength; cbn) in "Hprefix".
  have HsuffixLength : length suffix = 61%nat.
  { cbn [suffix]. rewrite length_drop HvaluesLength. lia. }
  iPoseProof (write_success_u64_array_to_uninit
    (bv_unsigned sp + 1136) suffix with "HvaluesRest") as
    "HvaluesRest".
  iEval (rewrite HsuffixLength; cbn) in "HvaluesRest".
  iDestruct (mem_mapsto_uninit_split 120 with "Htail") as
    "[Hmiddle Hwithdrawals]"; first lia.
  have HwithdrawalsAddress :
      bv_unsigned sp + 1624 + 120 = bv_unsigned sp + 1744 by lia.
  iEval (rewrite HwithdrawalsAddress) in "Hwithdrawals".
  iDestruct (mem_mapsto_uninit_split 48 with "Hwithdrawals") as
    "[Hwithdrawals Hsuffix]"; first lia.
  have HtailAddress :
      bv_unsigned sp + 1744 + 48 = bv_unsigned sp + 1792 by lia.
  iEval (rewrite HtailAddress) in "Hsuffix".
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 984)%I
    with "[Hgap Hprefix]" as "HupperPrefix".
  { iApply (mem_mapsto_uninit_combine 912 with "Hgap"); first lia.
    replace (bv_unsigned sp + 120 + 912) with
      (bv_unsigned sp + 1032) by lia.
    iExact "Hprefix". }
  iAssert ((bv_unsigned sp + 1136) ↦ₘ? 608)%I
    with "[HvaluesRest Hmiddle]" as "HupperSuffix".
  { iApply (mem_mapsto_uninit_combine 488 with "HvaluesRest"); first lia.
    replace (bv_unsigned sp + 1136 + 488) with
      (bv_unsigned sp + 1624) by lia.
    iExact "Hmiddle". }
  iAssert ((bv_unsigned sp + 1792) ↦ₘ? 104)%I
    with "[Hsuffix]" as "Htail".
  { replace (bv_unsigned sp + 1744 + 48) with
      (bv_unsigned sp + 1792) by lia.
    iExact "Hsuffix". }
  rewrite /writeSuccessTransactionsPuncturedScratch
    /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier.
  iFrame "Hlower Hbase Htotal HupperPrefix HupperSuffix Htail
    Hfirst Hsecond Hthird Hfourth Hcall Hitems Hwithdrawals".
  iPureIntro. exact Hfacts.
Qed.
