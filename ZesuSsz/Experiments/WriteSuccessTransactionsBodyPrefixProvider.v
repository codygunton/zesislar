From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBodyContract.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBodyPrefix.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBodyPrefixWitnessProvider.

Lemma write_success_transactions_body_prefix_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  writeSuccessTransactionsBodyPrefixContract P.
Proof.
  iIntros "#Hlookup #Hcode #Houtput #Hboolean #Hoptional #Hint128 #Hint64".
  rewrite /writeSuccessTransactionsBodyPrefixContract.
  iModIntro.
  rewrite /writeSuccessTransactionsBodyPrefixWitness.
  iApply (write_success_transactions_body_prefix_witness_provider P with
    "Hlookup Hcode Houtput Hboolean Hoptional Hint128 Hint64").
Qed.
