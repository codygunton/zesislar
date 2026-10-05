Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Section entry_application_0.
Context `{!islaG Sigma} `{!threadG}.
Context (domain : DecodeItemArgs -> Prop).
Context (args : DecodeItemArgs).
Check (ZesuSsz.Contracts.RlpDecodeItemContract.decodeItemEntryResources (args) (decodeItemC1BDomain) : iProp Sigma).
End entry_application_0.
Section entry_application_1.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974 (args) (frameBytes) : iProp Sigma).
End entry_application_1.
Section entry_application_2.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d697c (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_2.
Section entry_application_3.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (locals : DecodeItemReturnLocals).
Context (pointerBytes : list byte).
Context (lengthBytes : list byte).
Check (ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (locals) (pointerBytes) (lengthBytes) : iProp Sigma).
End entry_application_3.
Section entry_application_4.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69a4 (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_4.
Section entry_application_5.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (locals : DecodeItemReturnLocals).
Check (ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d69b0 (args) (locals) : iProp Sigma).
End entry_application_5.
Section entry_application_6.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69d8 (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_6.
Section entry_application_7.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e0 (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_7.
Section entry_application_8.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d69e8 (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_8.
Section entry_application_9.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a00 (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_9.
Section entry_application_10.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a08 (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_10.
Section entry_application_11.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (n : Z).
Context (payloadStart : Z).
Context (lengthBytes : list byte).
Context (frameBytes : list byte).
Context (oldAcc : bv 64).
Context (oldCursor : bv 64).
Context (loaded : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a14 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded) : iProp Sigma).
End entry_application_11.
Section entry_application_12.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Check (ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24 (args) : iProp Sigma).
End entry_application_12.
Section entry_application_13.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (n : Z).
Context (payloadStart : Z).
Context (lengthBytes : list byte).
Context (frameBytes : list byte).
Context (loaded : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) : iProp Sigma).
End entry_application_13.
Section entry_application_14.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (locals : DecodeItemReturnLocals).
Check (ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40 (args) (locals) : iProp Sigma).
End entry_application_14.
Section entry_application_15.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a64 (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_15.
Section entry_application_16.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a6c (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_16.
Section entry_application_17.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (locals : DecodeItemReturnLocals).
Check (ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a78 (args) (locals) : iProp Sigma).
End entry_application_17.
Section entry_application_18.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (frameBytes : list byte).
Context (x13 : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6aa8 (args) (frameBytes) (x13) : iProp Sigma).
End entry_application_18.
Section entry_application_19.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (n : Z).
Context (payloadStart : Z).
Context (lengthBytes : list byte).
Context (frameBytes : list byte).
Context (oldAcc : bv 64).
Context (oldCursor : bv 64).
Context (loaded : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ab4 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (oldAcc) (oldCursor) (loaded) : iProp Sigma).
End entry_application_19.
Section entry_application_20.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Check (ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6ac4 (args) : iProp Sigma).
End entry_application_20.
Section entry_application_21.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (n : Z).
Context (payloadStart : Z).
Context (lengthBytes : list byte).
Context (frameBytes : list byte).
Context (loaded : bv 64).
Check (ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ad8 (args) (n) (payloadStart) (lengthBytes) (frameBytes) (loaded) : iProp Sigma).
End entry_application_21.
Section entry_application_22.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (locals : DecodeItemReturnLocals).
Check (ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (locals) : iProp Sigma).
End entry_application_22.
Section entry_application_23.
Context `{!islaG Sigma} `{!threadG}.
Context (args : DecodeItemArgs).
Context (locals : DecodeItemReturnLocals).
Check (ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08 (args) (locals) : iProp Sigma).
End entry_application_23.
