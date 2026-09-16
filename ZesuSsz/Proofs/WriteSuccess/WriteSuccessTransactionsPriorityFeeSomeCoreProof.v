Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeSetup15124.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeCall15124.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeIntCall15134.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_priority_fee_some_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  instr_body 0x15148 (writeSuccessTransactionsPriorityFeePostSpec P) -∗
  instr_body 0x1511c
    (writeSuccessTransactionsPriorityFeeSomeCoreSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hboolean #Hint Hnext".
  iApply (write_success_transactions_priority_fee_some_setup_15124 P with
    "Hlookup Hcode").
  iApply (write_success_transactions_priority_fee_some_call_15124 P with
    "Hlookup Hcode Hboolean").
  iApply (write_success_transactions_priority_fee_some_int_call_15134 P with
    "Hlookup Hcode Hint Hnext").
Qed.
