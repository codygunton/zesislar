From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessLoopMemory.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

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

Global Instance : LithiumUnfold
    (@writeSuccessValueTransactionsContinuation) := I.
Global Instance : LithiumUnfold
    (@writeSuccessValueTransactionsEntry) := I.

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
