From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeFrameBounds.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeNonePrepared.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_priority_fee_none_setup_prepared
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15144 (writeSuccessTransactionsPriorityFeeNoneAt15144Spec P) -∗
  instr_body 0x1513c (writeSuccessTransactionsPriorityFeeNonePreparedSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try liARun.
  all: try iFrame.
  all: iIntros "Hsaved".
  all: iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  all: cbn.
  all: replace LET1 with (BV 64 0x16140) by bv_solve.
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try reflexivity; try assumption;
    try bv_solve; try lia; try done.
  all: rewrite /writeSuccessTransactionsPriorityFeeCallerFrame.
  all: iFrame.
Qed.

Lemma write_success_transactions_priority_fee_none_setup
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15144 (writeSuccessTransactionsPriorityFeeNoneAt15144Spec P) -∗
  instr_body 0x1513c (writeSuccessTransactionsPriorityFeeNoneCoreSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hnext".
  iPoseProof (write_success_transactions_priority_fee_none_setup_prepared P
    with "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iPoseProof (write_success_transactions_priority_fee_none_prepare P
    with "Hentry") as "Hprepared".
  iApply ("Hbody" with "Hprepared").
Qed.
