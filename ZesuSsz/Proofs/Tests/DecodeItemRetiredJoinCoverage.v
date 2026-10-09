Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Join6ae0From6a38.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Join6ae0From6ad8.
Open Scope Z_scope.

Lemma retiredJoin6a38Coverage `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoin6ae0From6a38 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest.
Proof.
  exact (decodeItemJoin6ae0From6a38_automatic args n payloadStart lengthBytes frameBytes loaded inputPrefix rest).
Qed.

Print Assumptions retiredJoin6a38Coverage.

Lemma retiredJoin6ad8Coverage `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (n payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoin6ae0From6ad8 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest.
Proof.
  exact (decodeItemJoin6ae0From6ad8_automatic args n payloadStart lengthBytes frameBytes loaded inputPrefix rest).
Qed.

Print Assumptions retiredJoin6ad8Coverage.

