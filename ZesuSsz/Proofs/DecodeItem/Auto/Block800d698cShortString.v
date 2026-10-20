Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import SailStdpp.MachineWord.

Lemma DesignedBoundary_800d698cShortString `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (x11 x12 x13 x14 x15 x16 : bv 64)
    (outputBytes frameBytes : list byte) (inputPrefix : byte) (rest : list byte) :
  decodeItemSelectedCode -∗
  instr_body 0x800d698c
    (decodeItemEntryAt800d698cShortString args x11 x12 x13 x14 x15 x16
      outputBytes frameBytes inputPrefix rest ∗ True)%I.
Proof.
  zesu_block.
Qed.
Print Assumptions DesignedBoundary_800d698cShortString.
