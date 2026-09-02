From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_14f08_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f1c (writeSuccessTransactionsAt14f1cSpec P) -∗
  instr_body 0x14f08 (writeSuccessTransactionsAt14f08Spec P).
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
      "(Hremaining & Hmmio & Htrace & HP & Hinv & Hexit & _)";
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
    iAssert (writeSuccessTransactionRestOwn transaction)
      with "[Haccess Hentries Hblob Hauthorizations]" as "HtransactionRest";
    [ iEval (unfold writeSuccessTransactionRestOwn); iFrame; done | ];
    iAssert (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)
      with "[HprefixMemory HremainingBytesExpected Hprocessed HdataOwn
        HtransactionRest HremainingOwn Hmmio Htrace HP Hexit]" as "HphaseFrame";
    [ iEval (unfold writeSuccessTransactionsCurrentPhaseFrame);
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
  all: iExists (tail,
    writeSuccessTransactionBytes transaction ++
      writeSuccessTransactionsBytes remaining,
    prefix, bytes, remaining, processed, transactions, transaction,
    base, sp, tt)ₗ.
  all: iSplit; first (iPureIntro; bv_solve).
  all: iEval (unfold writeSuccessTransactions14f1cFrame).
  all: cbn.
  all: iFrame.
  all: iFrame "HloadFacts"; done.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try done.
  Unshelve. all: try exact inhabitant.
Qed.
