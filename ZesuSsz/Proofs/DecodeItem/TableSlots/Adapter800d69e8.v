Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d69e8.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.

Lemma decodeItemSlotBody800d69e8 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d69e8 decodeItemState800d69e8.
Proof.
  apply decodeItemSlotBody800d69e8Conditional.
  intros args frameBytes x13 inputPrefix rest.
  iIntros "Hnext800d698c Hcode".
  iApply (DesignedBoundary_800d69e8 args frameBytes x13 inputPrefix rest with "[Hnext800d698c] Hcode").
  { iApply (instr_pre_wand with "Hnext800d698c []"); [done|done|].
    iIntros "(%next800d698c_x11 & %next800d698c_x12 & %next800d698c_x13 & %next800d698c_x14 & %next800d698c_x15 & %next800d698c_x16 & %next800d698c_outputBytes & %next800d698c_frameBytes & %next800d698c_pointerBytes & %next800d698c_lengthBytes & %next800d698c_inputPrefix & %next800d698c_rest & Hentry)".
    iAssert (ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698cShortString (args) (next800d698c_x11) (next800d698c_x12) (next800d698c_x13) (next800d698c_x14) (next800d698c_x15) (next800d698c_x16) (next800d698c_outputBytes) (next800d698c_frameBytes) (next800d698c_pointerBytes) (next800d698c_lengthBytes) (next800d698c_inputPrefix) (next800d698c_rest))%I with "[Hentry]" as "Hselected".
    { iExact "Hentry". }
    iExists next800d698c_x11, next800d698c_x12, next800d698c_x13, next800d698c_x14, next800d698c_x15, next800d698c_x16, next800d698c_outputBytes, next800d698c_frameBytes, next800d698c_pointerBytes, next800d698c_lengthBytes, next800d698c_inputPrefix, next800d698c_rest.
    rewrite /ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c.
    iFrame. }
Qed.
Print Assumptions decodeItemSlotBody800d69e8.
