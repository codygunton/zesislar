Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15048.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1505c.

Import ZesuSsz.Automation.Hooks.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15048
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1505c (writeSuccessTransactionsAt1505cSpec P) -∗
  instr_body 0x15048 (writeSuccessTransactionsAt15048Spec P).
Proof.
  zesu_block.
  Unshelve.
  iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  zesu_run.
  all: rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionWord.
  all: f_equal; f_equal; f_equal; f_equal; bv_solve.
Qed.

Print Assumptions write_success_transactions_chunk_15048.
