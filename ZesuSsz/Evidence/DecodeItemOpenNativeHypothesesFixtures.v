Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.bi Require Import bi.
Open Scope bi_scope.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Evidence.DecodeItemOpenNativeHypotheses.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Contracts.DecodeItemSelected.

Lemma decodeItemOpenNativeHypothesesApplication `{!islaG Sigma} `{!threadG}
  (H6a40 : decodeItemOpenNativeClosure6a40)
 :
  ⊢ □ decodeItemSelectedCode -∗ block_table_pre decodeItemBlockTable.
Proof.
  exact (decodeItemOpenNativeHypothesesTable
    (Build_DecodeItemOpenNativeHypotheses H6a40)).
Qed.

Print Assumptions decodeItemOpenNativeHypothesesApplication.


Lemma decodeItemOpenNativeMissing6a40Rejected
 : True.
Proof.
  Fail assert (Hopen : DecodeItemOpenNativeHypotheses) by (constructor; assumption).
  exact I.
Qed.
Print Assumptions decodeItemOpenNativeMissing6a40Rejected.
