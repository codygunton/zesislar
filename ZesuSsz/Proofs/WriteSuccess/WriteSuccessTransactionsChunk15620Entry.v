Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15620.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15628.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15620_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15628 (writeSuccessTransactionsAt15628Spec P) -∗
  instr_body 0x15620 (writeSuccessTransactionsAt15620Spec P).
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
  Unshelve. all: iIntros "Hdata Htransaction Houter"; liARun.
  all: iExists
    (tail, suffix, prefix, bytes, remaining, processed, transactions,
      base, tt)ₗ.
  all: iEval (unfold writeSuccessTransactions15628Frame).
  all: iDestruct "Houter" as
    "(Hremaining & Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  all: iDestruct select
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed)
    as "Hprocessed".
  all: iEval
    (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn)
    in "Hprocessed".
  all: iFrame.
  all: liARun.
  all: repeat iSplit; iPureIntro; try assumption; lia.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try bv_solve.
  all: try lia.
Qed.
