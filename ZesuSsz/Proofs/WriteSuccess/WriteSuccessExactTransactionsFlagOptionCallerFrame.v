Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagOptionEntry WriteSuccessExactTransactionsOptionSourcesRegion
  WriteSuccessExactTransactionsFieldFlagEntry WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsGasSignatureEntry.

Lemma transactions_flag_option_caller_frame `{!islaG Sigma} `{!threadG}
    sp row bytes index (P : iProp Sigma) :
  transactionFlagOptionRetained row bytes index
    (transactionFirstLoadRetained sp row bytes index (transactionOptionValuesCaller P)) ⊣⊢
  transactionOptionValuesCaller
    (transactionFlagOptionRetained row bytes index
      (transactionFirstLoadRetained sp row bytes index P)).
Proof.
  iStartProof. rewrite /transactionFlagOptionRetained /transactionFirstLoadRetained
    /transactionFieldFlagRetained /transactionSignatureFieldRetained
    /transactionGasSignatureRetained /transactionOptionValuesCaller.
  iSplit; iIntros "Hresources"; zesu_open_resource_groups.
  all: iFrame; repeat iSplit; done.
Qed.
Print Assumptions transactions_flag_option_caller_frame.

