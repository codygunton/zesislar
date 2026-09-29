Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeContract WriteSuccessRepresentation WriteSuccessValueSpec
  WriteSuccessOutputSemantic WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.Switches.ReturnBundle.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsChainEnd.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsSplit.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsPrefixJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
From IslaTraces.write_success_blocks Require Import Index.

Require Import ZesuSsz.Automation.Switches.LoadedTrace.
Require Import ZesuSsz.Proofs.WriteSuccess.InterfacesCoverage.
Require Import ZesuSsz.Automation.Switches.ConjunctMatch.
Lemma write_success_exact_post_withdrawals_before156f4
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntEntryBoundary -∗
  instr_body 0x156f4 (writeSuccessPostWithdrawalsAt156f4 args witness P) -∗
  instr_body 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)).
Proof.
  rewrite (write_success_exact_post_withdrawals_chain_end args witness Hwf).
  have HvaluesLength : length (writeSuccessValues witness) = 74%nat by (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  have HtakeLength : length (take 69 (writeSuccessValues witness)) = 69%nat by (rewrite length_take HvaluesLength; lia).
  time "before156f4_block" zesu_block.
  all: try (rewrite writeSuccessPostWithdrawals156f4Untouched_unfold
    writeSuccessPostWithdrawals156f4UntouchedRaw_unfold
    /WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataResources
    /WriteSuccessPostTransactionResources.writeSuccessDescriptorResources
    /WriteSuccessPostTransactionResources.writeSuccessHashesResources
    /writeSuccessNativeStaticResources
    /WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant).
  all: try (time "before156f4_frame" zesu_run).
Time Qed.
Print Assumptions write_success_exact_post_withdrawals_before156f4.
