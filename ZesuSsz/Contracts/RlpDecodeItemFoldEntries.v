From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.

(* The header entries retain the complete Q27 machine resources. *)
Definition decodeItemEntryAt800d6a24 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  (∃ n i payloadStart lengthBytes frameBytes loaded,
    decodeItemByteFoldStringHeader args n i payloadStart
      lengthBytes frameBytes loaded)%I.

Definition decodeItemEntryAt800d6ac4 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  (∃ n i payloadStart lengthBytes frameBytes loaded,
    decodeItemByteFoldListHeader args n i payloadStart
      lengthBytes frameBytes loaded)%I.

(* A body entry adds the loop guard without changing the header resources. *)
Definition decodeItemBodyAt800d6a24 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  (∃ n i payloadStart lengthBytes frameBytes loaded,
    ⌜i < n⌝ ∗
    decodeItemByteFoldStringHeader args n i payloadStart
      lengthBytes frameBytes loaded)%I.

Definition decodeItemBodyAt800d6ac4 `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) : iProp Sigma :=
  (∃ n i payloadStart lengthBytes frameBytes loaded,
    ⌜i < n⌝ ∗
    decodeItemByteFoldListHeader args n i payloadStart
      lengthBytes frameBytes loaded)%I.
