Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15628.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1562c.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15628_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x1562c (writeSuccessTransactionsAt1562cSpec P) -∗
  instr_body 0x15628 (writeSuccessTransactionsAt15628Spec P).
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
    (writeSuccessTransactions15628Frame sp base transaction transactions
      processed remaining bytes prefix suffix tail P) as "Hframe".
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iEval (unfold writeSuccessTransactions15628Frame) in "Hframe".
  all: iDestruct "Hframe" as (pointer)
    "(Hother & H8 & H9 & H18 & %Hpointer & Hlower & Hscratch & Hprefix & Hsuffix & Hprocessed &
     Htransaction & Hremaining & HP & Hinvariant & Hexit & _)".
  all: iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace & _)".
  all: have HstackAddress :
    bv_unsigned sp - 16 = bv_unsigned sp - 48 + 32 by lia.
  all: iEval (rewrite HstackAddress) in "Hstack".
  all: iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
    with "[Hlower Hstack]" as "Hlower48";
    [iApply (mem_mapsto_uninit_combine 32 with
       "[Hlower] [Hstack]"); [lia|iExact "Hlower"|iExact "Hstack"]|].
  all: liARun.
  all: iExists
    (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ.
  all: iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x1562c))%I
    with "[H1]" as "H1target".
  all: try (replace (BV 64 0x1562c) with
    (Z_to_bv 64 (87592 + 4)) by bv_solve; iExact "H1").
  all: iFrame.
  all: liARun.
  all: iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn).
  all: repeat iSplit; try iFrame; try iPureIntro; try assumption; try lia.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try bv_solve.
  all: try lia.
  Unshelve. all: lazymatch goal with |- ?G => fail "residual" G end.
Qed.
