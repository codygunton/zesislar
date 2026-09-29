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
Lemma write_success_exact_post_withdrawals_from156f4
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x156fc (writeSuccessExactPostWithdrawalsAt156fc args witness P) -∗
  instr_body 0x156f4 (writeSuccessPostWithdrawalsAt156f4 args witness P).
Proof.
  have HvaluesLength : length (writeSuccessValues witness) = 74%nat by (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  have HtakeLength : length (take 69 (writeSuccessValues witness)) = 69%nat by (rewrite length_take HvaluesLength; lia).
  time "from156f4_block" zesu_block.
  1: have Hindex : Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1144) -
      (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8) = 14%nat
      by (zesu_witness_facts; first [reflexivity | lia | bv_solve]).
  1: rewrite Hindex lookup_take in Hlookup; [rewrite /writeSuccessValueWord Hlookup; reflexivity | lia].
  all: try (rewrite writeSuccessPostWithdrawals156f4Untouched_unfold
    writeSuccessExactPostWithdrawalsUntouched_unfold
    writeSuccessExactPostWithdrawalsCallerFrame_unfold
    writeSuccessPostWithdrawals156f4UntouchedRaw_unfold
    /writeSuccessTerminalSavedSlots
    /WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant).
  all: time "from156f4_frame" (repeat iDestruct select (_ ∗ _)%I as "[? ?]"; iFrame).
Time Qed.
Print Assumptions write_success_exact_post_withdrawals_from156f4.
