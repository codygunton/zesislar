Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.Switches.ExistentialArrayRestore.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierPostLbu14fa0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierPostLbu14fa4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fa4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierState14fa8.

Lemma test_restore_carrier_14fa4 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  writeSuccessTransactionsAt14fa4CarrierSplitSpec P -∗
  writeSuccessTransactionsAt14fa4CarrierSpec P.
Proof.
  iStartProof.
  zesu_run.
Qed.
Print Assumptions test_restore_carrier_14fa4.

Lemma test_restore_carrier_14fa8 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  writeSuccessTransactionsAt14fa8CarrierSplitSpec P -∗
  writeSuccessTransactionsAt14fa8CarrierSpec P.
Proof.
  iStartProof.
  zesu_run.
Qed.
Print Assumptions test_restore_carrier_14fa8.
