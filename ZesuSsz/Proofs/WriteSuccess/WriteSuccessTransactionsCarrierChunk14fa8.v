From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f98.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14fa8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14fa8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14fb0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14fb0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f98.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Lemma write_success_transactions_carrier_chunk_14fa8
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14fb0 (writeSuccessTransactionsAt14fb0CarrierSpec P) -∗
  instr_body 0x14fa8 (writeSuccessTransactionsAt14fa8CarrierSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: iRename select
    (writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
      True)%I into "HfactsBundle".
  all: iDestruct "HfactsBundle" as "[Hfacts HfactsTrue]".
  all: iPoseProof "Hfacts" as "#HfactsCopy".
  all: iEval (unfold writeSuccessTransactionsLoadFacts) in "HfactsCopy".
  all: iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & HfactsCopyTrue)".
  all: iRename select
    (reg_col writeSuccessTransactions14fa8OtherRegShapes)%I into "Hother".
  all: iAssert (reg_col writeSuccessTransactions14fb0OtherRegShapes)%I
    with "[Hother]" as "HotherFinal"; [iExact "Hother" |].
  all: iRename select (reg_col zesu_ram_sys_regs)%I into "HsysFinal".
  all: iAssert (reg_col zesu_ram_sys_regs)%I with "[HsysFinal]"
    as "HsysBundled";
    [ rewrite /reg_col; iFrame;
      repeat iSplit; try iPureIntro; try reflexivity; try assumption; try done
    | ].
  all: iRename select
    (_ ↦ₘ∗ writeSuccessTransactionBytes transaction)%I into "HarrayFinal".
  all: iRename select (writeSuccessTransactionRestOwn transaction ∗ _)%I
    into "HphaseRest".
  all: iDestruct "HphaseRest" as "[Hrest HphaseRest]".
  all: iDestruct "HphaseRest" as "[Hremaining HphaseRest]".
  all: iDestruct "HphaseRest" as "[Hmmio HphaseRest]".
  all: iDestruct "HphaseRest" as "[Htrace HphaseRest]".
  all: iDestruct "HphaseRest" as "[HP HphaseRest]".
  all: iDestruct "HphaseRest" as "[Hinv HphaseRest]".
  all: iDestruct "HphaseRest" as "[Hexit HphaseTrue]".
  all: iRename select (base ↦ₘ∗ prefix)%I into "HbasePrefix".
  all: iRename select
    ((base + 288 * Z.of_nat (length processed) + 288) ↦ₘ∗
      writeSuccessTransactionsBytes remaining)%I into "HbaseSuffix".
  all: iRename select (writeSuccessTransactionsProcessedOwn processed)%I
    into "Hprocessed".
  all: iRename select
    ((match writeSuccessTransactionData transaction with
      | [] => _
      | _ :: _ => _
      end)%I) into "Hdata".
  all: iAssert (writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items)%I with
    "[HbasePrefix HbaseSuffix Hprocessed Hdata Hrest Hremaining Hmmio Htrace
      HP Hinv Hexit HphaseTrue]" as "HframeFinal";
    [ rewrite /writeSuccessTransactionsCurrentPhaseCarrierFrame;
      iSplitL "HbasePrefix"; [iExact "HbasePrefix" |];
      iSplitL "HbaseSuffix"; [iExact "HbaseSuffix" |];
      iSplitL "Hprocessed"; [iExact "Hprocessed" |];
      iSplitL "Hdata";
        [rewrite /writeSuccessByteArrayOwn; iExact "Hdata" |];
      iSplitL "Hrest"; [iExact "Hrest" |];
      iSplitL "Hremaining"; [iExact "Hremaining" |];
      iSplitL "Hmmio"; [iExact "Hmmio" |];
      iSplitL "Htrace"; [iExact "Htrace" |];
      iSplitL "HP"; [iExact "HP" |];
      iSplitL "Hinv"; [iExact "Hinv" |];
      iSplitL "Hexit"; [iExact "Hexit" |];
      iExact "HphaseTrue" | ].
  all: try (iAssert
    (writeSuccessTransactionsMachine14fb0Carrier
      sp base transactions processed transaction
      first second third fourth items)%I
    with "[-HarrayFinal HframeFinal]" as "HmachineFinal";
    [ rewrite /writeSuccessTransactionsMachine14fb0Carrier
        /writeSuccessTransactions14f98CarrierScratch;
      iSplitL "HsysBundled"; [iExact "HsysBundled" |];
      iSplitL "HotherFinal"; [iExact "HotherFinal" |];
      iFrame
    | ]).
  all: try iExists (items, fourth, third, second, first, tail, suffix, prefix,
    bytes, remaining, processed, transactions, transaction, base, sp, tt)ₗ.
  all: try cbn.
  all: try iFrame "HmachineFinal HarrayFinal HframeFinal".
  all: try rewrite /writeSuccessTransactionsLoadFacts.
  all: destruct H0 as
    (Hsecond & HitemsBound & HfirstAlign & HfirstLower & HfirstUpper &
      Hsp16Align & Hsp80Lower & HspRamUpper).
  all: repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
