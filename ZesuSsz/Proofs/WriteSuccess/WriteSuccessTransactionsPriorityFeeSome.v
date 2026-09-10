From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15148.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeMachineAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeCoreProof.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_priority_fee_some
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  instr_body 0x15148 (writeSuccessTransactionsAt15148Spec P) -∗
  instr_body 0x1511c
    (writeSuccessTransactionsPriorityFeeSomeAt1511cSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hboolean #Hint Hnext".
  iPoseProof (instr_pre_wand 0x15148 0x15148 false false
    (writeSuccessTransactionsAt15148Spec P)
    (writeSuccessTransactionsPriorityFeePostSpec P)
    with "Hnext") as "HnextCore"; [done | done | idtac].
  iSpecialize ("HnextCore" with "[]").
  { iIntros "Hpost".
    iApply write_success_transactions_priority_fee_post_adapter.
    iExact "Hpost". }
  iPoseProof (write_success_transactions_priority_fee_some_core P with
    "Hlookup Hcode Hboolean Hint HnextCore") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  rewrite instr_pre'_eq.
  iIntros "Hentry".
  iApply "Hbody".
  iApply write_success_transactions_priority_fee_some_entry_adapter.
  iExact "Hentry".
Qed.
