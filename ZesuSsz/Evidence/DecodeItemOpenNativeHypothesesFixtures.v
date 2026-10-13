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
  (H6960 : decodeItemOpenNativeClosure6960)
  (H69b0 : decodeItemOpenNativeClosure69b0)
  (H6a24 : decodeItemOpenNativeClosure6a24)
  (H6a38 : decodeItemOpenNativeClosure6a38)
  (H6a40 : decodeItemOpenNativeClosure6a40)
  (H6a78 : decodeItemOpenNativeClosure6a78)
  (H6aa8 : decodeItemOpenNativeClosure6aa8)
  (H6ac4 : decodeItemOpenNativeClosure6ac4)
  (H6ad8 : decodeItemOpenNativeClosure6ad8)
  (H6ae0 : decodeItemOpenNativeClosure6ae0)
 :
  ⊢ □ decodeItemSelectedCode -∗ block_table_pre decodeItemBlockTable.
Proof.
  exact (decodeItemOpenNativeHypothesesTable
    (Build_DecodeItemOpenNativeHypotheses H6960 H69b0 H6a24 H6a38 H6a40 H6a78 H6aa8 H6ac4 H6ad8 H6ae0)).
Qed.

Lemma decodeItemOpenNativeMissing6960Rejected
  (H69b0 : decodeItemOpenNativeClosure69b0)
  (H6a24 : decodeItemOpenNativeClosure6a24)
  (H6a38 : decodeItemOpenNativeClosure6a38)
  (H6a40 : decodeItemOpenNativeClosure6a40)
  (H6a78 : decodeItemOpenNativeClosure6a78)
  (H6aa8 : decodeItemOpenNativeClosure6aa8)
  (H6ac4 : decodeItemOpenNativeClosure6ac4)
  (H6ad8 : decodeItemOpenNativeClosure6ad8)
  (H6ae0 : decodeItemOpenNativeClosure6ae0)
 : True.
Proof.
  Fail assert (Hopen : DecodeItemOpenNativeHypotheses) by (constructor; assumption).
  exact I.
Qed.
Print Assumptions decodeItemOpenNativeHypothesesApplication.
Print Assumptions decodeItemOpenNativeMissing6960Rejected.
