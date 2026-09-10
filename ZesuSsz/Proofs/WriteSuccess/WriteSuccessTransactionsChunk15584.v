Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15584.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15620.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAuthorizationsAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15584Entry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1558cBranch.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15584
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15590
    (writeSuccessTransactionsAuthorizationsAnyLoopSpec P) -∗
  instr_body 0x15620 (writeSuccessTransactionsAt15620Spec P) -∗
  instr_body 0x15584 (writeSuccessTransactionsAt15584Spec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Hu256 #Hint #Houtput #Hauthloop Hnext".
  iPoseProof (write_success_transactions_chunk_1558c_branch P with
    "Hlookup Hcode Hmemcpy Hu256 Hint Houtput Hauthloop Hnext") as "Hbranch".
  iPoseProof (write_success_transactions_chunk_15584_entry P with
    "Hlookup Hcode Hbranch") as "Hcore".
  iApply (instr_pre_wand 0x15584 0x15584 false false with "Hcore");
    [done | done |].
  iApply write_success_transactions_15584_entry_adapter.
Qed.
