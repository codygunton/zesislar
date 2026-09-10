From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk1558cBranch.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBodyPrefixWitnessProvider.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopProvider.

Definition writeSuccessTransactionsLoopProviderEntryResources
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup ∗
   IslaTraces.write_success_blocks.Index.spec_instr_resources ∗
   □ instr_pre 0x101d4 zesuMemcpyCallSpec ∗
   □ instr_pre 0x10190 zesuWriteOutputCallSpec ∗
   □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) ∗
   □ instr_pre 0x15590
     (writeSuccessTransactionsAuthorizationsAnyLoopSpec P) ∗
   □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec ∗
   □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec ∗
   □ instr_pre 0x15c6c zesuEncoderBytesCallSpec ∗
   □ instr_pre 0x15cb0 zesuEncoderU256CallSpec ∗
   □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec ∗
   □ instr_pre 0x15d10 zesuEncoderIntCallSpec ∗
   □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) ∗ True)%I.

Lemma write_success_transactions_loop_provider_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsBodyPrefixWitness P -∗
  writeSuccessTransactionsLoopProviderEntryResources P -∗
  writeSuccessTransactionsLoopProviderResources P.
Proof.
  rewrite /writeSuccessTransactionsLoopProviderEntryResources.
  iIntros "Hprefix (#Hlookup & #Hcode & #Hmemcpy & #Houtput & #Hblob & #Hauth &
    #Hboolean & #Hoptional & #Hbytes & #Hu256 & #Hint128 & #Hint64 & #Hloop & _)".
  rewrite /writeSuccessTransactionsLoopProviderResources.
  iSplitL "Hprefix"; [iExact "Hprefix"|].
  iSplitL; [iExact "Hlookup"|].
  iSplitL; [iExact "Hcode"|].
  iSplitL; [iExact "Hmemcpy"|].
  iSplitL; [iExact "Houtput"|].
  iSplitL; [iExact "Hblob"|].
  iSplitL; [iExact "Hauth"|].
  iSplitL; [iExact "Hbytes"|].
  iSplitL; [iExact "Hu256"|].
  iSplitL; [iExact "Hint128"|].
  iSplitL; [iExact "Hint64"|].
  iSplitL; [iExact "Hloop"|].
  done.
Qed.
