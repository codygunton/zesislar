From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15620.

Import ListNotations.

Lemma writeSuccessTransactionsOwn_snoc `{!islaG Sigma}
    (processed : list writeSuccessTransaction)
    (transaction : writeSuccessTransaction) :
  writeSuccessTransactionsOwn processed -∗
  writeSuccessTransactionOwn transaction -∗
  writeSuccessTransactionsOwn (processed ++ [transaction]).
Proof.
  induction processed as [|head processed IH]; simpl.
  - iIntros "_ Htransaction". iFrame. done.
  - iIntros "Hprocessed Htransaction".
    iDestruct "Hprocessed" as "(Hhead & Hprocessed & _)".
    iFrame "Hhead".
    iPoseProof (IH with "Hprocessed Htransaction") as "Hsnoc".
    iFrame "Hsnoc".
Qed.

Lemma write_success_transactions_bytes_app
    (left right : list writeSuccessTransaction) :
  writeSuccessTransactionsBytes (left ++ right) =
    writeSuccessTransactionsBytes left ++
    writeSuccessTransactionsBytes right.
Proof.
  induction left as [|transaction left IH]; cbn.
  - reflexivity.
  - rewrite IH app_assoc. reflexivity.
Qed.

Lemma write_success_transactions_scratch_15620_to_loop
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
  writeSuccessTransactionsScratch15620
      sp base transactions processed transaction -∗
  writeSuccessTransactionsScratch sp base (length transactions).
Proof.
  iIntros "Hscratch".
  iEval (unfold writeSuccessTransactionsScratch15620,
    writeSuccessTransactionsScratch15620Tail) in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower48 & %HspAlign16 & %HspAlign8 & %HspLow & %HspHigh &
      Hsp104 & Hbase & Htotal & H120 & H128 & H136 & H144 & H152 &
      H160 & H168 & H176 & H184 & H192 & H200 & H208 & H216 & H224 &
      H232 & H240 & H248 & H256 & H264 & H272 & H280 & H1744 &
      H1888 & _)".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower48 Hsp104]" as "Hlower152".
  { iApply (mem_mapsto_uninit_combine 48 with "Hlower48").
    - lia.
    - have -> : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
      iExact "Hsp104". }
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H120") as "H120u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H128") as "H128u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H136") as "H136u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H144") as "H144u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H152") as "H152u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H160") as "H160u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H168") as "H168u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H176") as "H176u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H184") as "H184u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H192") as "H192u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H200") as "H200u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H208") as "H208u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H216") as "H216u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H224") as "H224u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H232") as "H232u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H240") as "H240u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H248") as "H248u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H256") as "H256u".
  iPoseProof (mem_mapsto_mapsto_to_uninit _ _ 64 with "H264") as "H264u".
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 16)%I
    with "[H120u H128u]" as "H120_16".
  { iApply (mem_mapsto_uninit_combine 8 with "H120u"); first lia.
    have -> : bv_unsigned sp + 120 + 8 = bv_unsigned sp + 128 by lia.
    iExact "H128u". }
  iAssert ((bv_unsigned sp + 136) ↦ₘ? 16)%I
    with "[H136u H144u]" as "H136_16".
  { iApply (mem_mapsto_uninit_combine 8 with "H136u"); first lia.
    have -> : bv_unsigned sp + 136 + 8 = bv_unsigned sp + 144 by lia.
    iExact "H144u". }
  iAssert ((bv_unsigned sp + 152) ↦ₘ? 16)%I
    with "[H152u H160u]" as "H152_16".
  { iApply (mem_mapsto_uninit_combine 8 with "H152u"); first lia.
    have -> : bv_unsigned sp + 152 + 8 = bv_unsigned sp + 160 by lia.
    iExact "H160u". }
  iAssert ((bv_unsigned sp + 168) ↦ₘ? 16)%I
    with "[H168u H176u]" as "H168_16".
  { iApply (mem_mapsto_uninit_combine 8 with "H168u"); first lia.
    have -> : bv_unsigned sp + 168 + 8 = bv_unsigned sp + 176 by lia.
    iExact "H176u". }
  iAssert ((bv_unsigned sp + 184) ↦ₘ? 16)%I
    with "[H184u H192u]" as "H184_16".
  { iApply (mem_mapsto_uninit_combine 8 with "H184u"); first lia.
    have -> : bv_unsigned sp + 184 + 8 = bv_unsigned sp + 192 by lia.
    iExact "H192u". }
  iAssert ((bv_unsigned sp + 200) ↦ₘ? 16)%I
    with "[H200u H208u]" as "H200_16".
  { iApply (mem_mapsto_uninit_combine 8 with "H200u"); first lia.
    have -> : bv_unsigned sp + 200 + 8 = bv_unsigned sp + 208 by lia.
    iExact "H208u". }
  iAssert ((bv_unsigned sp + 216) ↦ₘ? 16)%I
    with "[H216u H224u]" as "H216_16".
  { iApply (mem_mapsto_uninit_combine 8 with "H216u"); first lia.
    have -> : bv_unsigned sp + 216 + 8 = bv_unsigned sp + 224 by lia.
    iExact "H224u". }
  iAssert ((bv_unsigned sp + 232) ↦ₘ? 16)%I
    with "[H232u H240u]" as "H232_16".
  { iApply (mem_mapsto_uninit_combine 8 with "H232u"); first lia.
    have -> : bv_unsigned sp + 232 + 8 = bv_unsigned sp + 240 by lia.
    iExact "H240u". }
  iAssert ((bv_unsigned sp + 248) ↦ₘ? 16)%I
    with "[H248u H256u]" as "H248_16".
  { iApply (mem_mapsto_uninit_combine 8 with "H248u"); first lia.
    have -> : bv_unsigned sp + 248 + 8 = bv_unsigned sp + 256 by lia.
    iExact "H256u". }
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 32)%I
    with "[H120_16 H136_16]" as "H120_32".
  { iApply (mem_mapsto_uninit_combine 16 with "H120_16"); first lia.
    have -> : bv_unsigned sp + 120 + 16 = bv_unsigned sp + 136 by lia.
    iExact "H136_16". }
  iAssert ((bv_unsigned sp + 152) ↦ₘ? 32)%I
    with "[H152_16 H168_16]" as "H152_32".
  { iApply (mem_mapsto_uninit_combine 16 with "H152_16"); first lia.
    have -> : bv_unsigned sp + 152 + 16 = bv_unsigned sp + 168 by lia.
    iExact "H168_16". }
  iAssert ((bv_unsigned sp + 184) ↦ₘ? 32)%I
    with "[H184_16 H200_16]" as "H184_32".
  { iApply (mem_mapsto_uninit_combine 16 with "H184_16"); first lia.
    have -> : bv_unsigned sp + 184 + 16 = bv_unsigned sp + 200 by lia.
    iExact "H200_16". }
  iAssert ((bv_unsigned sp + 216) ↦ₘ? 32)%I
    with "[H216_16 H232_16]" as "H216_32".
  { iApply (mem_mapsto_uninit_combine 16 with "H216_16"); first lia.
    have -> : bv_unsigned sp + 216 + 16 = bv_unsigned sp + 232 by lia.
    iExact "H232_16". }
  iAssert ((bv_unsigned sp + 248) ↦ₘ? 24)%I
    with "[H248_16 H264u]" as "H248_24".
  { iApply (mem_mapsto_uninit_combine 16 with "H248_16"); first lia.
    have -> : bv_unsigned sp + 248 + 16 = bv_unsigned sp + 264 by lia.
    iExact "H264u". }
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 64)%I
    with "[H120_32 H152_32]" as "H120_64".
  { iApply (mem_mapsto_uninit_combine 32 with "H120_32"); first lia.
    have -> : bv_unsigned sp + 120 + 32 = bv_unsigned sp + 152 by lia.
    iExact "H152_32". }
  iAssert ((bv_unsigned sp + 184) ↦ₘ? 64)%I
    with "[H184_32 H216_32]" as "H184_64".
  { iApply (mem_mapsto_uninit_combine 32 with "H184_32"); first lia.
    have -> : bv_unsigned sp + 184 + 32 = bv_unsigned sp + 216 by lia.
    iExact "H216_32". }
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 128)%I
    with "[H120_64 H184_64]" as "H120_128".
  { iApply (mem_mapsto_uninit_combine 64 with "H120_64"); first lia.
    have -> : bv_unsigned sp + 120 + 64 = bv_unsigned sp + 184 by lia.
    iExact "H184_64". }
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 152)%I
    with "[H120_128 H248_24]" as "Hupper152".
  { iApply (mem_mapsto_uninit_combine 128 with "H120_128"); first lia.
    have -> : bv_unsigned sp + 120 + 128 = bv_unsigned sp + 248 by lia.
    iExact "H248_24". }
  iAssert ((bv_unsigned sp + 120) ↦ₘ? 1776)%I
    with "[Hupper152 H272 H280 H1744 H1888]" as "Hupper1776".
  { iApply (mem_mapsto_uninit_combine 152 with "Hupper152").
    - lia.
    - have -> : bv_unsigned sp + 120 + 152 = bv_unsigned sp + 272 by lia.
      iApply (mem_mapsto_uninit_combine 8 with "H272").
      + lia.
      + have -> : bv_unsigned sp + 272 + 8 = bv_unsigned sp + 280 by lia.
        iApply (mem_mapsto_uninit_combine 1464 with "H280").
        * lia.
        * have -> : bv_unsigned sp + 280 + 1464 = bv_unsigned sp + 1744 by lia.
          iApply (mem_mapsto_uninit_combine 144 with "H1744").
          -- lia.
          -- have -> : bv_unsigned sp + 1744 + 144 = bv_unsigned sp + 1888 by lia.
             iExact "H1888". }
  rewrite /writeSuccessTransactionsScratch.
  iFrame.
Qed.
