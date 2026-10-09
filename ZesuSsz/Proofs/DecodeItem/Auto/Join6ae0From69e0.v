Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Automation.SealedCoverage.
Open Scope Z_scope.

Lemma decodeItemJoin6ae0From69e0_automatic `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (frameBytes : list byte)
    (lengthRegister : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoin6ae0From69e0 args frameBytes lengthRegister inputPrefix rest.
Proof.
  zesu_block.
Qed.

Print Assumptions decodeItemJoin6ae0From69e0_automatic.
