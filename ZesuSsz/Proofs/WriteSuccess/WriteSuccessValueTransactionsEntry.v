Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Import ListNotations.

(** The entry separates one-time transaction resources from the preserved frame. *)
Definition writeSuccessValueTransactionsContinuation
    `{!islaG Sigma} (values : list (bv 64)) (payload : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗ P)%I.

Definition writeSuccessValueTransactionsEntry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) : iProp Sigma :=
  (writeSuccessValuePost sp values payload
      (writeSuccessTransactionsEvents sp transactions tail) P ∗
   bv_unsigned sp ↦ₘ? 104 ∗
   (bv_unsigned sp + 120) ↦ₘ? 912 ∗
   (bv_unsigned sp + 1624) ↦ₘ? 272 ∗
   base ↦ₘ∗ bytes ∗
   writeSuccessTransactionsOwn transactions ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions bytes tail
       (writeSuccessValueTransactionsContinuation values payload P)) ∗
   writeSuccessTransactionsInvariant sp base transactions [] transactions
     bytes [] bytes ∗
   ⌜length values = 74%nat⌝ ∗
   ⌜writeSuccessValueWord values 7 = Z_to_bv 64 base⌝ ∗
   ⌜writeSuccessValueWord values 8 =
      Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗ True)%I.

Definition writeSuccessValueTransactionsProviderFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (sourceBytes transactionBytes : list (bv 8)) : iProp Sigma :=
  (bv_unsigned sp ↦ₘ? 104 ∗
   (bv_unsigned sp + 120) ↦ₘ? 192 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ sourceBytes ∗
   (bv_unsigned sp + 1624) ↦ₘ? 272 ∗
   base ↦ₘ∗ transactionBytes ∗
   writeSuccessTransactionsOwn transactions ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions transactionBytes tail
       (writeSuccessValueTransactionsContinuation values payload P)) ∗
   writeSuccessTransactionsInvariant sp base transactions [] transactions
     transactionBytes [] transactionBytes ∗
   ⌜length sourceBytes = 720%nat⌝ ∗
   ⌜length values = 74%nat⌝ ∗
   ⌜writeSuccessValueWord values 7 = Z_to_bv 64 base⌝ ∗
   ⌜writeSuccessValueWord values 8 =
      Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessValueTransactionsContinuation) := I.
Global Instance : LithiumUnfold
    (@writeSuccessValueTransactionsEntry) := I.
Global Instance : LithiumUnfold
    (@writeSuccessValueTransactionsProviderFrame) := I.

Lemma write_success_value_transactions_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (sourceBytes transactionBytes : list (bv 8)) :
  writeSuccessValuePost sp values payload
    (writeSuccessTransactionsEvents sp transactions tail)
    (writeSuccessValueTransactionsProviderFrame P sp values payload tail base
      transactions sourceBytes transactionBytes) -∗
  writeSuccessValueTransactionsEntry P sp values payload tail base transactions
    transactionBytes.
Proof.
  iIntros "Hpost".
  iEval (rewrite /writeSuccessValuePost) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & Hother & H2 & H10 & H11 & Hlower & Hvalues & Hpayload &
      HbaseSlot & HcountSlot & Hmmio & Htrace & Hframe & _)".
  iEval (rewrite /writeSuccessValueTransactionsProviderFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hgap104 & Hgap192 & Hsource & Hgap272 &
      Harray & Hown & Hexit & Hinvariant & %HsourceLength &
      %HvaluesLength & %HbaseEq & %HcountEq & HP)".
  iPoseProof (write_success_byte_array_to_uninit with "Hsource") as
    "Hsource".
  iEval (rewrite HsourceLength) in "Hsource".
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 912)%I
    with "[Hgap192 Hsource]" as "Hgap912".
  { iApply (mem_mapsto_uninit_combine 192 with "Hgap192"); first lia.
    replace (bv_unsigned sp + 120 + 192) with
      (bv_unsigned sp + 312) by lia.
    iExact "Hsource". }
  rewrite /writeSuccessValueTransactionsEntry /writeSuccessValuePost.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.

(** Resources that the top-level proof must preserve through the header block. *)
Definition writeSuccessHeaderValueProviderResources
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 48 ∗
   bv_unsigned sp ↦ₘ? 104 ∗
   (bv_unsigned sp + 120) ↦ₘ? 192 ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
   base ↦ₘ∗ transactionBytes ∗
   writeSuccessTransactionsOwn transactions ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions transactionBytes tail
       (writeSuccessValueTransactionsContinuation values payload P)) ∗
   writeSuccessTransactionsInvariant sp base transactions [] transactions
     transactionBytes [] transactionBytes ∗
   ⌜length sourceBytes = 720%nat⌝ ∗
   ⌜bytes_of_u64s values = take 592 sourceBytes⌝ ∗
   ⌜length values = 74%nat⌝ ∗
   ⌜bv_unsigned (writeSuccessValueWord values 5) = length payload⌝ ∗
   ⌜writeSuccessValueWord values 7 = Z_to_bv 64 base⌝ ∗
   ⌜writeSuccessValueWord values 8 =
      Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Definition writeSuccessHeaderValueProviderFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) : iProp Sigma :=
  (writeSuccessHeaderValueProviderResources P sp sourceBytes values payload tail
      base transactions transactionBytes ∗
   instr_pre 0x14f04
     (writeSuccessValuePost sp values payload
       (writeSuccessTransactionsEvents sp transactions tail)
       (writeSuccessValueTransactionsProviderFrame P sp values payload tail
         base transactions sourceBytes transactionBytes)))%I.

Global Instance : LithiumUnfold
    (@writeSuccessHeaderValueProviderResources) := I.
Global Instance : LithiumUnfold
    (@writeSuccessHeaderValueProviderFrame) := I.

Lemma write_success_header_value_transactions_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) :
  writeSuccessHeaderPost sp sourceBytes
    (writeSuccessValueEvents sp values
      (writeSuccessTransactionsEvents sp transactions tail))
    (writeSuccessHeaderValueProviderFrame P sp sourceBytes values payload tail
      base transactions transactionBytes) -∗
  writeSuccessValueSpec
    (writeSuccessValueTransactionsProviderFrame P sp values payload tail base
      transactions sourceBytes transactionBytes).
Proof.
  iIntros "Hpost".
  iEval (rewrite /writeSuccessHeaderPost) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & Hother & H2 & Hfields & Hsource & Hcopied & Hgap272 &
      Hmmio & Htrace & Hframe & _)".
  iEval (rewrite /writeSuccessHeaderValueProviderFrame) in "Hframe".
  iDestruct "Hframe" as "[Hresources Hcontinue]".
  iEval (rewrite /writeSuccessHeaderValueProviderResources) in "Hresources".
  iDestruct "Hresources" as
    "(Hlower & Hgap104 & Hgap192 & Hpayload & Harray & Hown & Hexit &
      Hinvariant & %HsourceLength & %HvaluesBytes & %HvaluesLength &
      %HpayloadLength & %HbaseEq & %HcountEq & %Halign16 & %Halign8 &
      %HlowerBound & %HupperBound & HP & _)".
  iEval (rewrite -HvaluesBytes) in "Hcopied".
  iPoseProof (mem_mapsto_bytes_to_u64_array with "Hcopied") as "Hvalues".
  rewrite /writeSuccessValueSpec.
  iExists sp, values, payload,
    (writeSuccessTransactionsEvents sp transactions tail).
  iFrame "Hsys Hother H2 Hlower Hfields Hvalues Hpayload Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption.
  rewrite /writeSuccessValueTransactionsProviderFrame.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.

Lemma write_success_u64_array_to_uninit `{!islaG Sigma}
    (address : Z) (values : list (bv 64)) :
  address ↦ₘ∗ values -∗
  address ↦ₘ? (8 * Z.of_nat (length values)).
Proof.
  iIntros "Hvalues".
  iPoseProof (mem_mapsto_u64_array_to_bytes with "Hvalues") as "Hbytes".
  iPoseProof (write_success_byte_array_to_uninit with "Hbytes") as "Huninit".
  have Hlength :
      Z.of_nat (length (bytes_of_u64s values)) =
      8 * Z.of_nat (length values).
  { induction values as [|value values IH]; cbn [bytes_of_u64s].
    - reflexivity.
    - rewrite app_length length_bv_to_little_endian; [|lia].
      rewrite Nat2Z.inj_add IH. cbn. lia. }
  rewrite -Hlength. iExact "Huninit".
Qed.

Lemma write_success_value_transactions_entry_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) :
  writeSuccessValueTransactionsEntry P sp values payload tail base transactions
    bytes -∗
  writeSuccessTransactionsLoopSpec
    (writeSuccessValueTransactionsContinuation values payload P).
Proof.
  iIntros "Hentry".
  iEval (rewrite /writeSuccessValueTransactionsEntry /writeSuccessValuePost)
    in "Hentry".
  iDestruct "Hentry" as
    "((Hsys & Hother & H2 & H10 & H11 & Hlower48 & Hvalues & Hpayload &
       HbaseSlot & HcountSlot & Hmmio & Htrace & HP & _) & Hgap104 &
      Hgap912 & Hgap272 & Harray & Hown & Hexit & Hinvariant &
      %HvaluesLength & %HbaseEq & %HcountEq & _)".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower48 Hgap104]" as "Hlower".
  { iApply (mem_mapsto_uninit_combine 48 with "Hlower48"); first lia.
    replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by lia.
    iExact "Hgap104". }
  iPoseProof (write_success_u64_array_to_uninit with "Hvalues") as "Hvalues".
  iEval (rewrite HvaluesLength /=) in "Hvalues".
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 1504)%I
    with "[Hgap912 Hvalues]" as "HupperPrefix".
  { iApply (mem_mapsto_uninit_combine 912 with "Hgap912"); first lia.
    replace (bv_unsigned sp + 120 + 912) with (bv_unsigned sp + 1032) by lia.
    iExact "Hvalues". }
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 1776)%I
    with "[HupperPrefix Hgap272]" as "Hupper".
  { iApply (mem_mapsto_uninit_combine 1504 with "HupperPrefix"); first lia.
    replace (bv_unsigned sp + 120 + 1504) with
      (bv_unsigned sp + 1624) by lia.
    iExact "Hgap272". }
  iPoseProof "Hinvariant" as "#HinvKeep".
  iPoseProof "HinvKeep" as "#HinvFacts".
  iEval (rewrite /writeSuccessTransactionsInvariant) in "HinvFacts".
  iDestruct "HinvFacts" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %HbaseMin &
      %HbaseMax & _)".
  iAssert (base ↦ₘ∗ ([] : list (bv 8)))%I as "Hempty".
  { rewrite mem_mapsto_array_eq /mem_mapsto_array_def /=.
    iExists 1%N. iSplit; first done.
    iSplit; last done. iPureIntro. lia. }
  rewrite /writeSuccessTransactionsLoopSpec
    /writeSuccessTransactionsScratch
    /writeSuccessValueTransactionsContinuation.
  iExists sp, base, transactions, ([] : list writeSuccessTransaction),
    transactions, bytes, ([] : list (bv 8)), bytes, tail.
  change (default (BV 64 0) (values !! 7%nat) = Z_to_bv 64 base)
    in HbaseEq.
  change (default (BV 64 0) (values !! 8%nat) =
    Z_to_bv 64 (Z.of_nat (length transactions))) in HcountEq.
  rewrite HbaseEq HcountEq.
  rewrite /writeSuccessTransactionsOwn /=.
  cbn.
  rewrite Z.mul_0_r Z.add_0_r.
  iAssert (("x11" ↦ᵣ RVal_Bits (Z_to_bv 64 0))%I)
    with "[H11]" as "H11Zero".
  { replace (Z_to_bv 64 0) with (BV 64 0) by bv_solve. iExact "H11". }
  iFrame "Hsys Hother H2 H10 H11Zero Hempty Harray Hown Hlower HbaseSlot
    HcountSlot Hupper Hmmio Htrace Hpayload HP HinvKeep Hexit".
Qed.
