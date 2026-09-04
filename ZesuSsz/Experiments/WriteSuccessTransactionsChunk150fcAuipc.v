From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15100.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15104.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150fcAuipcBlock.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15100_auipc
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15104 (writeSuccessTransactionsAt15104Spec P) -∗
  instr_body 0x15100 (writeSuccessTransactionsAt15100Spec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15100Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix
      tail) "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (instr_pre_wand 0x15104 0x15104 false false
    (writeSuccessTransactionsAt15104Spec P)
    (writeSuccessTransactionsAt15104Block P sp base transaction transactions
      processed remaining bytes prefix suffix tail)
    with "Hnext") as "HnextBlock"; [done | done | idtac].
  iSpecialize ("HnextBlock" with "[]").
  { iIntros "Hblock".
    rewrite /writeSuccessTransactionsAt15104Spec.
    iExists sp, base, transaction, transactions, processed, remaining, bytes,
      prefix, suffix, tail.
    iExact "Hblock". }
  iPoseProof (write_success_transactions_chunk_15100_auipc_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode HnextBlock") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply ("Hbody" with "Hentry").
Qed.
