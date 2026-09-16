Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15154.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions15154To15158.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactions15158Branches.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15154
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P) -∗
  instr_body 0x15154 (writeSuccessTransactionsAt15154Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Hboolean #Houtput Hnext".
  iPoseProof (write_success_transactions_15158_branches P
    with "Hlookup Hcode Hboolean Houtput Hnext") as "H15158".
  iApply (write_success_transactions_15154_to_15158 P
    with "Hlookup Hcode H15158").
Qed.
