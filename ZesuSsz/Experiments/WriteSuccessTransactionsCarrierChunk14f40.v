From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f3c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f40.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f44.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.
#[local] Typeclasses Opaque writeSuccessTransactionsInvariant.

Lemma write_success_transactions_carrier_chunk_14f40
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f44 (writeSuccessTransactionsAt14f44CarrierSpec P) -∗
  instr_body 0x14f40 (writeSuccessTransactionsAt14f40CarrierSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?".
  iRename select
    (writeSuccessTransactions14f3cCarrierScratch sp base _ _ transaction
      first second third fourth items)%I into "Hscratch".
  iEval (unfold writeSuccessTransactions14f3cCarrierScratch) in "Hscratch".
  iDestruct "Hscratch" as
    "(HscratchLower & HstackBase & HstackTotal & Hstack & Hstack144 &
      Hstack136 & HstackProcessed & HscratchUpper & Hcarrier &
      Hscratch1136 & Hscratch1744 & Hscratch1792)".
  iDestruct (mem_mapsto_uninit_split 104 with "Hstack") as
    "[HstackLower HstackStore]"; first lia.
  have HstackStoreAddress : bv_unsigned sp + 120 + 104 =
      bv_unsigned sp + 224 by lia.
  iEval (rewrite HstackStoreAddress; simpl) in "HstackStore".
  iRename select
    (writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
      True)%I into "HfactsBundle".
  iDestruct "HfactsBundle" as "[Hfacts Htrue]".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "HfactsCopy".
  iDestruct "HfactsCopy" as "[%Hlength HfactsCopy]".
  iDestruct "HfactsCopy" as "[%HcurrentAlign HfactsCopy]".
  iDestruct "HfactsCopy" as "[%HcurrentLower HfactsCopy]".
  iDestruct "HfactsCopy" as "[%HcurrentUpper HfactsCopy]".
  iDestruct "HfactsCopy" as "[%HspAlign HfactsCopy]".
  iDestruct "HfactsCopy" as "[%HspLower HfactsCopy]".
  iDestruct "HfactsCopy" as "[%HspUpper HfactsTrue]".
  liARun.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try done.
  Unshelve. all: try exact inhabitant.
  Unshelve.
  iRename select (writeSuccessTransactionRestOwn transaction ∗ _)%I
    into "HphaseRest".
  iDestruct "HphaseRest" as "[Hrest HphaseRest]".
  iDestruct "HphaseRest" as "[Hremaining HphaseRest]".
  iDestruct "HphaseRest" as "[Hmmio HphaseRest]".
  iDestruct "HphaseRest" as "[Htrace HphaseRest]".
  iDestruct "HphaseRest" as "[HP HphaseRest]".
  iDestruct "HphaseRest" as "[Hinv HphaseRest]".
  iDestruct "HphaseRest" as "[Hexit HphaseTrue]".
  iRename select (base ↦ₘ∗ prefix)%I into "HbasePrefix".
  iRename select
    ((base + 288 * Z.of_nat (length processed) + 288) ↦ₘ∗
      writeSuccessTransactionsBytes remaining)%I into "HbaseSuffix".
  iRename select (writeSuccessTransactionsProcessedOwn processed)%I
    into "Hprocessed".
  iRename select
    ((match writeSuccessTransactionData transaction with
      | [] => _
      | _ :: _ => _
      end)%I) into "Hdata".
  iAssert (writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items)%I with
    "[HbasePrefix HbaseSuffix Hprocessed Hdata Hrest Hremaining Hmmio Htrace
      HP Hinv Hexit HphaseTrue]" as "Hphase".
  { rewrite /writeSuccessTransactionsCurrentPhaseCarrierFrame
      /writeSuccessTransactionPhaseEvents /writeSuccessByteArrayOwn.
    iFrame. }
  iEval (unfold writeSuccessTransactionsAt14f44CarrierSpec).
  iExists
    (items, fourth, third, second, first, tail, suffix, prefix, bytes,
      remaining, transactions, tt)ₗ.
  cbn.
  rewrite /writeSuccessTransactions14f44CarrierScratch.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
