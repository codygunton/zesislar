Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Automation.SealedCoverage.
Open Scope Z_scope.

Lemma decodeItemJoin6ae0From6a38_automatic `{!islaG Sigma} `{!threadG} (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoin6ae0From6a38 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest.
Proof.
  zesu_block.
Qed.

Print Assumptions decodeItemJoin6ae0From6a38_automatic.
