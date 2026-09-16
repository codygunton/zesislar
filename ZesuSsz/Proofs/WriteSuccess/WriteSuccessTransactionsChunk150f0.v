Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150fc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f0Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f8SomeCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f8NoneCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f0SomeEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f0NoneEntry.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_150f0_some
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64SomeCallSpec -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0SomeSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hsome Hnext".
  iPoseProof (write_success_transactions_chunk_150f8_some_call with
    "Hlookup Hcode Hsome Hnext") as "Hcall".
  iApply (write_success_transactions_chunk_150f0_some_entry with
    "Hlookup Hcode Hcall").
Qed.

Lemma write_success_transactions_chunk_150f0_none
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64NoneCallSpec -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0NoneSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hnone Hnext".
  iPoseProof (write_success_transactions_chunk_150f8_none_call with
    "Hlookup Hcode Hnone Hnext") as "Hcall".
  iApply (write_success_transactions_chunk_150f0_none_entry with
    "Hlookup Hcode Hcall").
Qed.

Lemma write_success_transactions_chunk_150f0_valid
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0ValidSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hoptional Hnext".
  iAssert (□ (True -∗
    instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec))%I
    with "[]" as "#HoptionalHidden".
  { iModIntro. iIntros "_". iExact "Hoptional". }
  iAssert (□ instr_pre 0x15bc8 zesuEncoderOptionalU64SomeCallSpec)%I
    with "[]" as "HsomeCall".
  { iModIntro.
    iSpecialize ("HoptionalHidden" with "[]"). { done. }
    iApply (instr_pre_wand 0x15bc8 0x15bc8 true true
      zesuEncoderOptionalU64CallSpec zesuEncoderOptionalU64SomeCallSpec
      with "HoptionalHidden"); [done | done |].
    iIntros "Hsome". iLeft. iExact "Hsome". }
  iAssert (□ instr_pre 0x15bc8 zesuEncoderOptionalU64NoneCallSpec)%I
    with "[]" as "HnoneCall".
  { iModIntro.
    iSpecialize ("HoptionalHidden" with "[]"). { done. }
    iApply (instr_pre_wand 0x15bc8 0x15bc8 true true
      zesuEncoderOptionalU64CallSpec zesuEncoderOptionalU64NoneCallSpec
      with "HoptionalHidden"); [done | done |].
    iIntros "Hnone". iRight. iExact "Hnone". }
  iClear "Hoptional HoptionalHidden".
  rewrite instr_pre'_eq.
  iIntros "Hentry".
  iPoseProof (write_success_transactions_150f0_branch_adapter with "Hentry")
    as "[Hsome|Hnone]".
  - iPoseProof (write_success_transactions_chunk_150f0_some P) as "Hproof".
    iEval (rewrite instr_pre'_eq) in "Hproof".
    iPoseProof ("Hproof" with "Hlookup Hcode HsomeCall Hnext") as "Hbody".
    iApply ("Hbody" with "Hsome").
  - iPoseProof (write_success_transactions_chunk_150f0_none P) as "Hproof".
    iEval (rewrite instr_pre'_eq) in "Hproof".
    iPoseProof ("Hproof" with "Hlookup Hcode HnoneCall Hnext") as "Hbody".
    iApply ("Hbody" with "Hnone").
Qed.

Lemma write_success_transactions_chunk_150f0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcSpec P) -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0Spec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hoptional Hnext".
  iPoseProof (instr_pre_wand 0x150fc 0x150fc false false
    (writeSuccessTransactionsAt150fcSpec P)
    (writeSuccessTransactionsAt150fcFramedSpec P) with "Hnext")
    as "HnextFramed"; [done | done |].
  iSpecialize ("HnextFramed" with "[]").
  { iApply (write_success_transactions_150fc_return_adapter P). }
  iPoseProof (write_success_transactions_chunk_150f0_valid P with
    "Hlookup Hcode Hoptional HnextFramed") as "Hbody".
  iApply (instr_pre_wand 0x150f0 0x150f0 false false
    (writeSuccessTransactionsAt150f0ValidSpec P)
    (writeSuccessTransactionsAt150f0Spec P) with "Hbody");
    [done | done |].
  iApply (write_success_transactions_150f0_valid_adapter P).
Qed.
