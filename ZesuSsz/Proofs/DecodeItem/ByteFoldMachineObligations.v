Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.

Definition decodeItemStringFoldEntry `{!islaG Sigma} `{!threadG} :=
  decodeItemFoldEntryObligation false.
Definition decodeItemStringFoldPreservation `{!islaG Sigma} `{!threadG} :=
  decodeItemFoldPreservationObligation false.
Definition decodeItemStringFoldExit `{!islaG Sigma} `{!threadG} :=
  decodeItemFoldExitObligation false.
Definition decodeItemListFoldEntry `{!islaG Sigma} `{!threadG} :=
  decodeItemFoldEntryObligation true.
Definition decodeItemListFoldPreservation `{!islaG Sigma} `{!threadG} :=
  decodeItemFoldPreservationObligation true.
Definition decodeItemListFoldExit `{!islaG Sigma} `{!threadG} :=
  decodeItemFoldExitObligation true.
