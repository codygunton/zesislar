From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk1558cBranch.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBodyPrefixWitnessProvider.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopCompose.

Definition writeSuccessTransactionsLoopProviderResources
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (writeSuccessTransactionsBodyPrefixWitness P ∗
   instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup ∗
   IslaTraces.write_success_blocks.Index.spec_instr_resources ∗
   □ instr_pre 0x101d4 zesuMemcpyCallSpec ∗
   □ instr_pre 0x10190 zesuWriteOutputCallSpec ∗
   □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) ∗
   □ instr_pre 0x15590
     (writeSuccessTransactionsAuthorizationsAnyLoopSpec P) ∗
   □ instr_pre 0x15c6c zesuEncoderBytesCallSpec ∗
   □ instr_pre 0x15cb0 zesuEncoderU256CallSpec ∗
   □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec ∗
   □ instr_pre 0x15d10 zesuEncoderIntCallSpec ∗
   □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) ∗ True)%I.

Lemma write_success_transactions_loop_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsLoopProviderResources P -∗
  instr_body 0x14f04 (writeSuccessTransactionsLoopSpec P).
Proof.
  rewrite /writeSuccessTransactionsLoopProviderResources.
  iIntros "(Hprefix & #Hlookup & #Hcode & #Hmemcpy & #Houtput & #Hblob &
    #Hauth & #Hbytes & #Hu256 & #Hint128 & #Hint64 & #Hloop & _)".
  iApply (write_success_transactions_loop_compose P with
    "Hprefix Hlookup Hcode Hmemcpy Houtput Hblob Hauth Hbytes Hu256 Hint128
      Hint64 Hloop").
Qed.
