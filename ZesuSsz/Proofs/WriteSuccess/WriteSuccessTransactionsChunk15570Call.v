Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15570.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15574.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15570_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  instr_body 0x15574 (writeSuccessTransactionsAt15574Spec P) -∗
  instr_body 0x15570 (writeSuccessTransactionsAt15570Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try liARun.
  all: iDestruct select
    (writeSuccessTransactions15570Frame sp base transaction transactions
      processed remaining bytes prefix suffix tail pointer P) as "Hframe".
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iEval (unfold writeSuccessTransactions15570Frame) in "Hframe".
  all: iDestruct "Hframe" as
    "(Hother & H19 & H22 & %Halign16 & %Halign8 & %HspMin & %HspMax &
     Hscratch & %Hpointer & Hprefix & Hsuffix & Hprocessed & Htransaction &
     Hremaining & HP & Hinvariant & Hexit & _)".
  all: iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace & _)".
  all: liARun.
  all: iExists
    (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ.
  all: iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x15574))%I
    with "[H1]" as "H1target".
  all: try (replace (BV 64 0x15574) with
    (Z_to_bv 64 (87408 + 4)) by bv_solve; iExact "H1").
  all: iFrame.
  all: liARun.
  all: iEval
    (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn).
  all: repeat iSplit; try iFrame; try iPureIntro; try assumption; try lia.
Qed.
