Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15580.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15584.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15580_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x15584 (writeSuccessTransactionsAt15584Spec P) -∗
  instr_body 0x15580 (writeSuccessTransactionsAt15580Spec P).
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
    (writeSuccessTransactions15580Frame sp base transaction transactions
      processed remaining bytes prefix suffix tail pointer P) as "Hframe".
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iEval (unfold writeSuccessTransactions15580Frame) in "Hframe".
  all: iDestruct "Hframe" as
    "(Hother & H18 & H19 & H22 & %Halign16 & %Halign8 & %HspMin & %HspMax &
     HstackLow & Hscratch & %Hpointer & Hprefix & Hsuffix & Hprocessed &
     Htransaction & Hremaining & HP & Hinvariant & Hexit & _)".
  all: iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & HstackHigh & Hmmio & Htrace & _)".
  all: have HstackAddress :
    bv_unsigned sp - 16 = bv_unsigned sp - 32 + 16 by lia.
  all: iEval (rewrite HstackAddress) in "HstackHigh".
  all: iAssert ((bv_unsigned sp - 32) ↦ₘ? 32)%I
    with "[HstackLow HstackHigh]" as "Hstack";
    [iApply (mem_mapsto_uninit_combine 16 with
       "[HstackLow] [HstackHigh]");
     [lia|iExact "HstackLow"|iExact "HstackHigh"]|].
  all: liARun.
  all: iExists
    (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ.
  all: iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x15584))%I
    with "[H1]" as "H1target".
  all: try (replace (BV 64 0x15584) with
    (Z_to_bv 64 (87424 + 4)) by bv_solve; iExact "H1").
  all: iFrame.
  all: iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn).
  all: repeat iSplit; try iFrame; try iPureIntro; try assumption; try lia.
Qed.
