From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15668WithdrawalsTotalStates.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1566cWithdrawalsTotal.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_post_15668_withdrawals_total
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (transactionBase withdrawalBase : Z)
    (transactions : list writeSuccessTransaction) (transactionBytes : list (bv 8))
    (count : nat) (withdrawalBytes : list (bv 8)) (tail : spec)
    (first second : bv 64) (items : list ByteListItem) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x1566c
    (writeSuccessTransactionsPost1566cWithdrawalsTotalSpec P sp pointer
      transactionBase withdrawalBase transactions transactionBytes count
      withdrawalBytes tail first second items) -∗
  instr_body 0x15668
    (writeSuccessTransactionsPost15668WithdrawalsTotalSpec P sp pointer
      transactionBase withdrawalBase transactions transactionBytes count
      withdrawalBytes tail first second items).
Proof.
  move => *. iStartProof. iIntros "#Hlookup Hnext".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try exact inhabitant.
  all: try bv_solve.
  Unshelve.
Qed.
