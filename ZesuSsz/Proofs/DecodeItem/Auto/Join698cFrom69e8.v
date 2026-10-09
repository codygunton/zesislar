Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Automation.SealedCoverage.
Open Scope Z_scope.

Lemma decodeItemJoin698cFrom69e8_automatic `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte)
    (payloadLength : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoin698cFrom69e8 args frameBytes payloadLength inputPrefix rest.
Proof.
  zesu_block.
Qed.

Print Assumptions decodeItemJoin698cFrom69e8_automatic.
