From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsCarrierState14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopCarrierEntry.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_carrier_chunk_14f08
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f1c (writeSuccessTransactionsAt14f1cCarrierSpec P) -∗
  instr_body 0x14f08 (writeSuccessTransactionsAt14f08CarrierSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: iIntros "Hdata HtransactionRest HphaseRest".
  all: (
    iRename select (base ↦ₘ∗ prefix)%I into "HprefixMemory";
    iRename select
      ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix)%I
      into "HsuffixMemory";
    iRename select (writeSuccessTransactionsProcessedOwn processed)%I
      into "Hprocessed";
    iDestruct "HtransactionRest" as
      "(Haccess & Hentries & Hblob & Hauthorizations & %Hvalid & _)";
    iDestruct "HphaseRest" as
      "(Hremaining & Hcarrier & Hwithdrawals & Hmmio & Htrace & HP & Hinv &
        Hexit & _)";
    iAssert (writeSuccessByteArrayOwn
      (writeSuccessTransactionDataPointer transaction)
      (writeSuccessTransactionData transaction))
      with "[Hdata]" as "HdataOwn";
    [ iEval (unfold writeSuccessByteArrayOwn); iExact "Hdata" | ];
    iAssert (writeSuccessTransactionsOwn remaining)
      with "[Hremaining]" as "HremainingOwn";
    [ iEval (unfold writeSuccessTransactionsOwn); iExact "Hremaining" | ];
    iDestruct "Hinv" as "#Hinv";
    iPoseProof (write_success_transactions_current_load_facts
      sp base transaction transactions processed remaining bytes prefix suffix
      Hvalid with "Hinv") as "[HloadFacts %Hsuffix]";
    iPoseProof "HloadFacts" as "#HloadFactsCopy";
    iEval (unfold writeSuccessTransactionsLoadFacts) in "HloadFactsCopy";
    iDestruct "HloadFactsCopy" as
      "(%HtransactionLength & %HcurrentAlign & %HcurrentLower &
       %HcurrentUpper & %HspAlign & %HspLower & %HspUpper & _)";
    iDestruct (mem_mapsto_array_app 8%N
      (base + 288 * Z.of_nat (length processed)) (DfracOwn 1)
      (writeSuccessTransactionBytes transaction)
      (writeSuccessTransactionsBytes remaining) with "[HsuffixMemory]")
      as "[HtransactionBytes HremainingBytes]";
    [ rewrite -Hsuffix /=; iExact "HsuffixMemory" | ];
    iEval (rewrite HtransactionLength /=) in "HremainingBytes";
    iAssert ((base + 288 * Z.of_nat (length processed) + 288) ↦ₘ∗
      writeSuccessTransactionsBytes remaining)%I
      with "[HremainingBytes]" as "HremainingBytesExpected";
    [ iExact "HremainingBytes" | ];
    iDestruct (mem_mapsto_array_app 8%N
      (base + 288 * Z.of_nat (length processed)) (DfracOwn 1)
      ([] : list (bv 8)) (writeSuccessTransactionBytes transaction)
      with "[HtransactionBytes]") as "[HemptyPrefix HtransactionBytes]";
    [ iExact "HtransactionBytes" | ];
    iAssert (writeSuccessTransactionRestOwn transaction)
      with "[Haccess Hentries Hblob Hauthorizations]" as "HtransactionRest";
    [ iEval (unfold writeSuccessTransactionRestOwn); iFrame; done | ];
    iAssert (writeSuccessTransactionsCurrentPhaseCarrierFrame P sp base
      transaction transactions processed remaining bytes prefix suffix tail
      first second third fourth items)
      with "[HprefixMemory HremainingBytesExpected Hprocessed HdataOwn
        HtransactionRest HremainingOwn Hmmio Htrace HP Hexit]" as "HphaseFrame";
    [ iEval (unfold writeSuccessTransactionsCurrentPhaseCarrierFrame);
      iFrame "HprefixMemory HremainingBytesExpected Hprocessed HdataOwn
        HtransactionRest HremainingOwn Hmmio Htrace HP Hinv Hexit"; done | ];
    liARun).
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: iEval (unfold writeSuccessTransactionsAt14f1cCarrierSpec).
  all: iExists (items, fourth, third, second, first, tail,
    writeSuccessTransactionBytes transaction ++
      writeSuccessTransactionsBytes remaining,
    prefix, bytes, remaining, processed, transactions, transaction,
    base, sp, tt)ₗ.
  all: cbn.
  all: iEval (unfold writeSuccessTransactionsMachine14f1cCarrier;
    unfold writeSuccessTransactions14f1cCarrierScratch).
  all: cbn.
  all: iFrame "HloadFacts HemptyPrefix HphaseFrame Hcarrier Hwithdrawals".
  all: iFrame.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try done.
  Unshelve. all: try exact inhabitant.
  all: try done.
  all: have Hzero : (1 * 0 = 0)%Z by lia.
  all: iEval (rewrite Hzero Z.add_0_r) in "HtransactionBytes".
  all: have HscratchAddress :
    bv_unsigned sp + 248 + 8 = bv_unsigned sp + 256 by lia.
  all: have HcurrentValue :
    LET3 = Z_to_bv 64 (base + 288 * Z.of_nat (length processed)) by bv_solve.
  all: iRename select ((bv_unsigned sp + 248 + 8) ↦ₘ? 848)%I
    into "HscratchUpper".
  all: iRename select ("x10" ↦ᵣ RVal_Bits LET3)%I into "H10Current".
  all: iEval (rewrite HscratchAddress) in "HscratchUpper".
  all: iEval (rewrite HcurrentValue) in "H10Current".
  all: iFrame "HscratchUpper H10Current HtransactionBytes".
Qed.
