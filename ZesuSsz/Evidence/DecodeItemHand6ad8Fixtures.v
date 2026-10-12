Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ad8.

Lemma decodeItemHand6ad8ExactBoundary `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte)   :
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  instr_pre 0x800d6b08 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_headerLength : Z) (successor_payloadLength : Z), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08 (args) (successor_locals) (successor_inputPrefix) (successor_rest) (successor_headerLength) (successor_payloadLength))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ad8
    (DesignedEntry_800d6ad8 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest).
Proof. exact (@DesignedBoundary_800d6ad8 Sigma islaG0 H args n payloadStart lengthBytes frameBytes loaded inputPrefix rest). Qed.
Print Assumptions decodeItemHand6ad8ExactBoundary.
