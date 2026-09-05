From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14fc8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState15028.
Require Import IslaTraces.write_success_32.a15028_spec.

Import WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Lemma write_success_transactions_carrier_chunk_15028_store
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1502c (writeSuccessTransactionsAt15028CarrierSpec P) -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028CarrierSpec P).
Proof.
  iIntros "#Hlookup #_ Hnext".
  iPoseProof "Hlookup" as "#Hlookup15028".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15028".
  iPoseProof ("Hlookup15028" $! 0x15028) as "Hinstr".
  iSpecialize ("Hinstr" with "[]").
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15028.
    done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15028) in "Hinstr".
  iPoseProof (IslaTraces.write_success_32.a15028_spec.a15028_spec 0x15028
    with "Hinstr") as "Hsd".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15028CarrierSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail first second third fourth items)
    "(Hmachine & Harray & Hphase & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite /writeSuccessTransactionsMachine15028Carrier) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & Hx2 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 & Hx10 &
      Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 & Hx19 &
      Hx20 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 & Hx30 &
      Hx31 & Hscratch & _)".
  iEval (rewrite
    /WriteSuccessTransactionsCarrierState14fc8.writeSuccessTransactions14fc8CarrierScratch)
    in "Hscratch".
  iDestruct "Hscratch" as
    "(Hlower & H104 & H112 & H120 & H128 & H224 & H232 & H240 & H248 &
      H256 & H272 & H280 & Hcarrier & H1136 & H1664 & H1672 & H1680 &
      H1744 & H1792)".
  iDestruct (mem_mapsto_uninit_split 8 with "H128") as "[H128 H136]".
  { lia. }
  iApply ("Hsd" with "[-]").
  rewrite /zesu_sd_spec /rv64_sd_spec.
  iExists (writeSuccessTransactionWord transaction 64), sp.
  iFrame "Hsys Hx29 Hx2 H128".
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro; lia.
  rewrite instr_pre'_eq.
  iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(HsysPost & Hx29Post & Hx2Post & H128Post & _)".
  iPoseProof (mem_mapsto_mapsto_to_uninit with "H128Post") as "H128Uninit".
  iAssert ((bv_unsigned sp + 128) ↦ₘ? 96)%I
    with "[H128Uninit H136]" as "H128Final".
  { iApply (mem_mapsto_uninit_combine 8 with "H128Uninit"); first lia.
    have -> : (bv_unsigned sp + 128 + 8 = bv_unsigned sp + 136)%Z by lia.
    iExact "H136". }
  iAssert (writeSuccessTransactionsMachine15028Carrier sp base transactions
      processed transaction first second third fourth items)%I
    with "[-Harray Hphase Hnext]" as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine15028Carrier
      /WriteSuccessTransactionsCarrierState14fc8.writeSuccessTransactions14fc8CarrierScratch.
    iFrame "HsysPost Hother Hx2Post Hx5 Hx6 Hx7 Hx8 Hx9 Hx10 Hx11 Hx12
      Hx13 Hx14 Hx15 Hx16 Hx17 Hx18 Hx19 Hx20 Hx23 Hx24 Hx25 Hx26 Hx27
      Hx28 Hx29Post Hx30 Hx31 Hlower H104 H112 H120 H128Final H224 H232
      H240 H248 H256 H272 H280 Hcarrier H1136 H1664 H1672 H1680 H1744
      H1792". }
  iAssert (writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes)%I as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply "Hnext".
  rewrite /writeSuccessTransactionsAt15028CarrierSpec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail, first, second, third, fourth, items.
  iFrame "HmachineFinal Harray Hphase HfactsFinal".
Qed.
