Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneSetup.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_priority_fee_none_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x15148 (writeSuccessTransactionsPriorityFeePostSpec P) -∗
  instr_body 0x1513c
    (writeSuccessTransactionsPriorityFeeNoneCoreSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hboolean Hnext".
  iApply (write_success_transactions_priority_fee_none_setup P with
    "Hlookup Hcode").
  iApply (write_success_transactions_priority_fee_none_call P with
    "Hlookup Hcode Hboolean Hnext").
Qed.
