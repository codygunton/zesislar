From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a4To151a8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a8To151ac.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Remove Hints find_body_a151a4_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_151a4_to_151ac
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x151ac (writeSuccessTransactionsAt151acSpec P) -∗
  instr_body 0x151a4 (writeSuccessTransactionsAt151a4Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_chunk_151a8_to_151ac P
    with "Hlookup Hcode Hnext") as "H151a8".
  iApply (write_success_transactions_chunk_151a4_to_151a8 P
    with "Hlookup Hcode H151a8").
Qed.
