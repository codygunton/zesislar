Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14fe0Loads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fc8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fe4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14ff0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15018.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState15028.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseCarrierFrame.

Lemma write_success_transactions_carrier_chunk_14ff0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15018 (writeSuccessTransactionsAt15018CarrierSpec P) -∗
  instr_body 0x14ff0 (writeSuccessTransactionsAt14ff0CarrierSpec P).
Proof.
  move => *.
  iStartProof.
  liARun.
  destruct (WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction)
    eqn:Hdata;
    liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: have Hx7Post : LET16 =
      bv_or
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 268))
          (BV 64 24))
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 267))
          (BV 64 16)) by bv_solve.
  all: have Hx12Post : LET14 =
      bv_or
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 266))
          (BV 64 8))
        (bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 265)) by bv_solve.
  all: have Hx13Post : LET12 =
      bv_or
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 280))
          (BV 64 24))
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 279))
          (BV 64 16)) by bv_solve.
  all: have Hx19Post : LET4 =
      bv_shiftl
        (bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 266))
        (BV 64 8) by bv_solve.
  all: have Hx28Post : LET18 =
      bv_or
        (bv_shiftl
          (bv_zero_extend 64
            (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
              transaction 270))
          (BV 64 8))
        (bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
            transaction 269)) by bv_solve.
  all: iRename select ("x7" ↦ᵣ RVal_Bits LET16)%I into "Hx7Post".
  all: iRename select ("x12" ↦ᵣ RVal_Bits LET14)%I into "Hx12Post".
  all: iRename select ("x13" ↦ᵣ RVal_Bits LET12)%I into "Hx13Post".
  all: iRename select ("x19" ↦ᵣ RVal_Bits LET4)%I into "Hx19Post".
  all: iRename select ("x28" ↦ᵣ RVal_Bits LET18)%I into "Hx28Post".
  all: iEval (rewrite Hx7Post) in "Hx7Post".
  all: iEval (rewrite Hx12Post) in "Hx12Post".
  all: iEval (rewrite Hx13Post) in "Hx13Post".
  all: iEval (rewrite Hx19Post) in "Hx19Post".
  all: iEval (rewrite Hx28Post) in "Hx28Post".
  all: iRename select
    ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)%I
    into "Harray".
  all: iRename select
    (base ↦ₘ∗ WriteSuccessTransactionsSpec.writeSuccessTransactionsBytes
      processed)%I into "HbasePrefix".
  all: iRename select
    ((base + 288 * Z.of_nat (length processed) + 288) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionsBytes remaining)%I
    into "HbaseSuffix".
  all: iRename select
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn
      processed)%I into "Hprocessed".
  2: iRename select
    (bv_unsigned
      (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer
        transaction) ↦ₘ∗ (b :: l))%I into "HdataMem".
  2: iAssert
    (WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn
      (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer
        transaction)
      (WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction))%I
    with "[HdataMem]" as "HdataFinal";
    [ rewrite /WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn Hdata;
      iFrame "HdataMem";
      repeat iSplit; try iPureIntro; try assumption; try done
    | ].
  1: iAssert
    (WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn
      (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer
        transaction)
      (WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction))%I
    as "HdataFinal";
    [ rewrite /WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn Hdata;
      done
    | ].
  all: iRename select
    (writeSuccessTransactionRestOwn transaction)%I
    into "Hrest".
  all: fold WriteSuccessTransactionsSpec.writeSuccessTransactionsOwn in *.
  all: iRename select
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsOwn remaining)%I
    into "Hremaining".
  all: iRename select (mmio_range (machineOutputAddress defaultMap) 16)%I into "Hmmio".
  all: iRename select (spec_trace _)%I into "Htrace".
  all: iEval (simpl) in "Htrace".
  all: iRename select P%I into "HP".
  all: iRename select
    (instr_pre WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExitAddress
      (writeSuccessTransactionsLoopCarrierExit P sp base
        (processed ++ transaction :: remaining)
        (WriteSuccessTransactionsSpec.writeSuccessTransactionsBytes
          (processed ++ transaction :: remaining)) tail
        first second third fourth items))%I into "Hexit".
  all: iAssert (writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base
    transaction (processed ++ transaction :: remaining) processed remaining
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsBytes
      (processed ++ transaction :: remaining))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsBytes processed)
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ++
      WriteSuccessTransactionsSpec.writeSuccessTransactionsBytes remaining)
    tail first second third fourth items)%I with
    "[HbasePrefix HbaseSuffix Hprocessed HdataFinal Hrest Hremaining Hmmio
      Htrace HP Hexit]" as "Hphase";
    [ rewrite /writeSuccessTransactionsCurrentPhaseCarrierFrame
        /WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant Hdata;
      simpl;
      iFrame "HbasePrefix HbaseSuffix Hprocessed HdataFinal Hrest Hremaining
        Hmmio";
      iSplitL "Htrace";
      [ rewrite Hdata; simpl; iExact "Htrace"
      | ];
      iFrame "HP Hexit";
      repeat iSplit; try iPureIntro; try assumption; try done
    | ].
  all: iExists (items, fourth, third, second, first, tail,
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ++
      WriteSuccessTransactionsSpec.writeSuccessTransactionsBytes remaining),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsBytes processed),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsBytes
      (processed ++ transaction :: remaining)), remaining,
    (processed ++ transaction :: remaining), transaction, sp, tt)ₗ.
  all: iSplitR "Harray Hphase";
  [
    iIntros "(HsysFinal & Hx10Final & Hx18Final & Hx20Final & Hx29Final &
      Hx27Final)";
    rewrite /writeSuccessTransactionsMachine15028Carrier
      /WriteSuccessTransactionsCarrierState14fc8.writeSuccessTransactions14fc8CarrierScratch;
    iFrame;
    try prepare_sidecond;
    try bv_solve;
    try iFrame
  |
    iFrame;
    rewrite /writeSuccessTransactionsLoadFacts;
    repeat iSplit; try iPureIntro; try assumption; done
  ].
  Unshelve.
  all: iPureIntro.
  all: assumption.
Qed.
